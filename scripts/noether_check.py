#!/usr/bin/env python3
"""Inventory the current checkout; optionally rebuild its local Lean graph serially.

Python 3.11+, standard library only. A successful inventory is NOT Lean evidence.
Build mode checks the source's explicit #print axioms commands, not every
compiler-generated declaration or the completeness of a historical paper.
"""
from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = 'leanprover/lean4:v4.31.0'
MATHLIB = 'fabf563a7c95a166b8d7b6efca11c8b4dc9d911f'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
NAME = r'[A-Za-z_][A-Za-z_0-9.\u0080-\uffff\']*'


def require(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def lean_code(text: str) -> str:
    """Mask nested comments and strings, preserving line breaks for source scans.

    This is deliberately not a Lean parser; compilation remains authoritative.
    The repository uses ordinary imports and one-name #print axioms commands.
    """
    out: list[str] = []
    depth = 0
    string = False
    i = 0
    while i < len(text):
        ch = text[i]
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; out.extend('  '); i += 2
            elif pair == '-/':
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if ch == '\n' else ' '); i += 1
        elif string:
            if ch == '\\':
                out.extend('  '); i += 2
            else:
                string = ch != '"'
                out.append('\n' if ch == '\n' else ' '); i += 1
        elif pair == '/-':
            depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            end = text.find('\n', i)
            end = len(text) if end == -1 else end
            out.extend(' ' * (end-i)); i = end
        elif ch == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(ch); i += 1
    require(not depth and not string, 'Unterminated Lean comment/string')
    return ''.join(out)


def imports_and_targets(text: str) -> tuple[list[str], list[str]]:
    code = lean_code(text)
    imports = []
    targets = []
    for line in code.splitlines():
        stripped = line.strip()
        if stripped.startswith('import '):
            names = stripped[7:].split()
            require(all(re.fullmatch(NAME, n) for n in names), 'Unsupported import syntax')
            imports.extend(names)
        if stripped.startswith('#print axioms'):
            match = re.fullmatch(r'#print\s+axioms\s+(' + NAME + r')\s*', stripped)
            require(match is not None, 'Unsupported #print axioms syntax')
            targets.append(match.group(1))
    require(not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|debug\.skipKernelTC', code),
            'Source contains a proof-escape token: requires explicit review')
    return imports, targets


def topological_order(graph: dict[str, list[str]], root: str) -> list[str]:
    result: list[str] = []
    visiting: set[str] = set()
    done: set[str] = set()
    def visit(name: str) -> None:
        require(name in graph, f'Missing local module: {name}')
        require(name not in visiting, f'Local import cycle at {name}')
        if name in done:
            return
        visiting.add(name)
        for dependency in graph[name]:
            visit(dependency)
        visiting.remove(name)
        done.add(name)
        result.append(name)
    visit(root)
    require(done == set(graph), f'Local files outside root import graph: {sorted(set(graph)-done)}')
    return result


def read_tsv(path: Path, key: str) -> list[dict[str, str]]:
    with path.open(encoding='utf-8-sig', newline='') as stream:
        reader = csv.DictReader(stream, delimiter='\t')
        require(reader.fieldnames is not None and key in reader.fieldnames, f'Missing {key}: {path}')
        rows = list(reader)
    require(all(None not in row and all(v is not None for v in row.values()) for row in rows),
            f'Malformed TSV row: {path}')
    ids = [r[key] for r in rows]
    require(all(ids) and len(ids) == len(set(ids)), f'Empty/duplicate {key}: {path}')
    return rows


def inventory(root: Path = ROOT) -> dict:
    toolchain = (root/'lean-toolchain').read_text().strip()
    require(toolchain == TOOLCHAIN, 'Toolchain changed: review the verification configuration')
    manifest = json.loads((root/'lake-manifest.json').read_text())
    packages = manifest['packages']
    require(len({p['name'] for p in packages}) == len(packages), 'Duplicate dependency name')
    require(all(p['type'] == 'git' and re.fullmatch(r'[0-9a-f]{40}', p['rev']) for p in packages),
            'Every resolved dependency must have an immutable Git commit')
    mathlib = next(p for p in packages if p['name'] == 'mathlib')
    require(mathlib['rev'] == MATHLIB, 'Mathlib lock changed: explicit revalidation required')
    config = tomllib.loads((root/'lakefile.toml').read_text())
    direct = config['require']
    require(len(direct) == 1 and direct[0]['name'] == 'mathlib', 'Unexpected direct dependencies')
    require(direct[0]['git'] == mathlib['url'], 'Mathlib origin mismatch')
    require(direct[0]['rev'] == mathlib['inputRev'], 'Lake requirement/lock mismatch')
    sources = [root/'MathematicalCommons.lean', *sorted((root/'MathematicalCommons').rglob('*.lean'))]
    modules = {}
    for path in sources:
        require(path.is_file() and not path.is_symlink(), f'Missing/symlinked source: {path}')
        raw = path.read_bytes()
        name = path.relative_to(root).with_suffix('').as_posix().replace('/', '.')
        imports, targets = imports_and_targets(raw.decode('utf-8-sig'))
        modules[name] = {'path': path.relative_to(root).as_posix(),
                         'sha256': hashlib.sha256(raw).hexdigest(),
                         'imports': imports, 'axiom_targets': targets}
    graph = {n: [i for i in m['imports'] if i == 'MathematicalCommons' or i.startswith('MathematicalCommons.')]
             for n, m in modules.items()}
    order = topological_order(graph, 'MathematicalCommons')
    works = read_tsv(root/'metadata/noether-works.tsv', 'work_id')
    claims = read_tsv(root/'metadata/noether-theorems.tsv', 'id')
    known = {w['work_id'] for w in works}
    require(all(c['work_id'] in known for c in claims), 'Claim refers to an unknown work')
    return {'schema': 'noether-check/1', 'toolchain': toolchain, 'mathlib': mathlib['rev'],
            'lean_executed': False, 'direct_noether_imports': len(graph['MathematicalCommons.Noether']),
            'local_modules': len(modules), 'explicit_axiom_commands': sum(len(m['axiom_targets']) for m in modules.values()),
            'works': len(works), 'work_states': dict(sorted(Counter(w['coverage_state'] for w in works).items())),
            'claim_rows': len(claims), 'coverage_states': dict(sorted(Counter(c['mathlib_coverage'] for c in claims).items())),
            'local_contribution_states': dict(sorted(Counter(c['local_contribution'] for c in claims).items())),
            'build_status_states': dict(sorted(Counter(c['build_status'] for c in claims).items())),
            'count_caveat': 'Rows are inventoried claims/packages, not theorem or discovery counts. Ledger status is historical metadata, not a current proof result.',
            'build_order': order, 'modules': modules}


def check_axioms(text: str, targets: list[str]) -> dict[str, list[str]]:
    pattern = r"'([^\n]+)'\s+depends on axioms:\s*\[([^\]]*)\]|'([^\n]+)'\s+does not depend on any axioms"
    reports = []
    for m in re.finditer(pattern, text):
        name = m.group(1) or m.group(3)
        axioms = [a.strip() for a in (m.group(2) or '').split(',') if a.strip()]
        require(set(axioms) <= ALLOWED_AXIOMS, f'Nonstandard axiom in {name}: {axioms}')
        reports.append((name, axioms))
    require(len(reports) == len(targets), f'Expected {len(targets)} axiom reports; got {len(reports)}')
    # Each command emits one report in source order. Qualified names are printed by Lean.
    for target, (actual, _) in zip(targets, reports):
        require(actual == target or actual.endswith('.'+target), f'Axiom target mismatch: {target} / {actual}')
    require(len({name for name, _ in reports}) == len(reports), 'Duplicate axiom report in module')
    return dict(reports)


def resolved_dependencies(root: Path = ROOT) -> None:
    manifest = json.loads((root/'lake-manifest.json').read_text())
    for p in manifest['packages']:
        path = root/manifest['packagesDir']/p['name']
        head = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        require(head == p['rev'], f'Resolved revision mismatch: {p["name"]}')
        changes = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True)
        require(not changes.strip(), f'Tracked dependency modifications: {p["name"]}')


def rebuild(report: dict, output: Path, strict_files: list[str], root: Path = ROOT) -> None:
    resolved_dependencies(root)
    require(set(strict_files) <= {m['path'] for m in report['modules'].values()}, 'Unknown --strict-file')
    # Ask Lake for only the environment needed by Lean, without publishing secrets.
    code = 'import os,json; print(json.dumps({k:os.environ[k] for k in ["PATH","LEAN_PATH","LEAN_SYSROOT","LD_LIBRARY_PATH","DYLD_LIBRARY_PATH"] if k in os.environ}))'
    configured = json.loads(subprocess.check_output(['lake', 'env', sys.executable, '-c', code], cwd=root, text=True))
    env = dict(os.environ, **configured)
    objects = output/'olean'
    require(not objects.exists(), f'Refusing to reuse prior local objects: use a fresh --output directory ({objects})')
    objects.mkdir(parents=True)
    env['LEAN_PATH'] = str(objects) + os.pathsep + env.get('LEAN_PATH', '')
    env['LEAN_NUM_THREADS'] = '1'
    report['lean_version'] = subprocess.check_output(['lean', '--version'], cwd=root, env=env, text=True).strip()
    report['lean_executed'] = True
    report['build_success'] = False
    report['checked_modules'] = []
    logs = output/'logs'
    logs.mkdir(exist_ok=True)
    for number, name in enumerate(report['build_order'], 1):
        entry = report['modules'][name]
        target = objects/Path(entry['path']).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        command = ['lean', '--trust=0']
        if entry['path'] in strict_files:
            command += ['-DwarningAsError=true']
        command += ['-o', str(target), entry['path']]
        print(f'[{number}/{report["local_modules"]}] {name}', flush=True)
        start = time.monotonic()
        run = subprocess.run(command, cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, timeout=600)
        logfile = logs/(name+'.log')
        logfile.write_text(run.stdout, encoding='utf-8')
        record = {'module': name, 'source_sha256': entry['sha256'], 'exit_code': run.returncode,
                  'seconds': round(time.monotonic()-start, 3), 'log': logfile.relative_to(output).as_posix(),
                  'log_sha256': hashlib.sha256(logfile.read_bytes()).hexdigest()}
        report['checked_modules'].append(record)
        (output/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
        if run.returncode:
            print(run.stdout, file=sys.stderr)
        require(run.returncode == 0, f'Lean failed: {name}')
        require(target.exists(), f'Lean did not write the requested object: {name}')
        record['axioms'] = check_axioms(run.stdout, entry['axiom_targets'])
        record['warnings'] = [line for line in run.stdout.splitlines() if 'warning:' in line]
    report['build_success'] = True
    report['axiom_scope'] = 'Every explicit source #print axioms command in the local root graph; not all declarations or historical claims.'


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'.noether-check')
    parser.add_argument('--resolved', action='store_true')
    parser.add_argument('--build', action='store_true')
    parser.add_argument('--strict-file', action='append', default=[])
    args = parser.parse_args()
    report = None
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    try:
        report = inventory()
        (output/'inventory.json').write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps({k:v for k,v in report.items() if k not in {'modules','build_order'}}, indent=2))
        if args.resolved:
            resolved_dependencies()
        if args.build:
            rebuild(report, output, args.strict_file)
            (output/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
        return 0
    except (ValueError, OSError, KeyError, StopIteration, subprocess.SubprocessError) as exc:
        if report is not None:
            report['build_success'] = False
            report['error'] = str(exc)
            (output/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
        print(f'NOETHER CHECK FAILED: {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
