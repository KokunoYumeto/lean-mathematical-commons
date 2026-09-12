"""Checker regression tests. These do not prove any Lean theorem."""
from pathlib import Path
import sys
import hashlib
import json
import re
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
from noether_check import check_axioms, imports_and_targets, inventory, lean_code, read_tsv, topological_order, TOOLCHAIN, MATHLIB


class ScannerTests(unittest.TestCase):
    def test_comments_and_strings(self):
        text = '/- import Wrong /- sorry -/ -/\nimport A B -- ignored\n#eval "sorry"\n#print axioms t\n'
        self.assertEqual(imports_and_targets(text), (['A', 'B'], ['t']))

    def test_line_numbers(self):
        source = '/- a\nb /- c -/ -/\n#eval "x\\\"y"\n'
        self.assertEqual(source.count('\n'), lean_code(source).count('\n'))

    def test_unclosed_comment(self):
        with self.assertRaises(ValueError): lean_code('/- broken')

    def test_proof_escape(self):
        for word in ('sorry', 'admit', 'axiom', 'native_decide', 'unsafe'):
            with self.subTest(word=word), self.assertRaises(ValueError):
                imports_and_targets('theorem x : True := by '+word)

    def test_bad_command(self):
        with self.assertRaises(ValueError): imports_and_targets('#print axioms')


class GraphTests(unittest.TestCase):
    def test_shared_dependency(self):
        self.assertEqual(topological_order({'R':['A','B'], 'A':['C'], 'B':['C'], 'C':[]}, 'R'),
                         ['C','A','B','R'])

    def test_cycle(self):
        with self.assertRaises(ValueError): topological_order({'A':['B'],'B':['A']}, 'A')

    def test_missing(self):
        with self.assertRaises(ValueError): topological_order({'A':['B']}, 'A')

    def test_orphan(self):
        with self.assertRaises(ValueError): topological_order({'A':[],'B':[]}, 'A')


class AxiomTests(unittest.TestCase):
    def test_standard_multiline(self):
        self.assertEqual(check_axioms("'N.t' depends on axioms:\n[propext,\n Quot.sound]\n", ['t']),
                         {'N.t':['propext','Quot.sound']})

    def test_no_axioms_and_prime(self):
        self.assertEqual(check_axioms("'N.t'' does not depend on any axioms", ["t'"]), {"N.t'":[]})

    def test_missing(self):
        with self.assertRaises(ValueError): check_axioms('', ['t'])

    def test_extra(self):
        with self.assertRaises(ValueError): check_axioms("'t' depends on axioms: []", [])

    def test_wrong_target(self):
        with self.assertRaises(ValueError): check_axioms("'N.other' depends on axioms: []", ['t'])

    def test_duplicate(self):
        with self.assertRaises(ValueError): check_axioms("'t' depends on axioms: []\n"*2, ['t','t'])

    def test_nonstandard(self):
        for axiom in ('sorryAx','Lean.ofReduceBool','Project.assumption'):
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                check_axioms(f"'t' depends on axioms: [{axiom}]", ['t'])


class LedgerTests(unittest.TestCase):
    def test_duplicate_and_malformed_rows(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)/'x.tsv'
            for text in ('id\tv\na\t1\na\t2\n', 'id\tv\na\n', 'id\tv\na\t1\t2\n'):
                path.write_text(text)
                with self.subTest(text=text), self.assertRaises(ValueError): read_tsv(path, 'id')

    def test_valid(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)/'x.tsv'
            path.write_text('id\tv\na\t1\n')
            self.assertEqual(read_tsv(path, 'id'), [{'id':'a','v':'1'}])


class RepositoryTests(unittest.TestCase):
    def test_current_document_links(self):
        root = Path(__file__).resolve().parents[1]
        for name in ('README.md', 'BUILDING.md', 'CONTRIBUTING.md', 'docs/noether/README.md'):
            page = root/name
            for link in re.findall(r'\[[^\]]+\]\(([^)]+)\)', page.read_text()):
                if '://' in link or link.startswith('#'):
                    continue
                with self.subTest(page=name, link=link):
                    self.assertTrue((page.parent/link.split('#')[0]).exists())

    def test_historical_readme_preserved(self):
        root = Path(__file__).resolve().parents[1]
        raw = (root/'README.checkpoint-20260829.md').read_bytes()
        self.assertEqual(hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest(),
                         '053c0a29734bbcbf1ef7efffec593f2fa4885506')

    def test_manifest_configuration_regression(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root/'lean-toolchain').write_text(TOOLCHAIN+'\n')
            (root/'lake-manifest.json').write_text(json.dumps({'packages': [
                {'type':'git', 'rev':MATHLIB, 'name':'mathlib', 'configFile':'lakefile.toml'}]}))
            with self.assertRaisesRegex(ValueError, 'configuration filename'):
                inventory(root)


if __name__ == '__main__':
    unittest.main()
