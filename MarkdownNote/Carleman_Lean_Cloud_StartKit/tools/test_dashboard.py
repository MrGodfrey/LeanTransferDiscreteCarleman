"""Regression cases for the review's concrete failure modes. Fixtures are synthetic."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import update_dashboard as dashboard
from validate_lean_project import validate_project

ROOT = Path(__file__).resolve().parents[1]
SHA = 'a' * 40
OTHER = 'b' * 40
URL = 'https://github.com/example/project/actions/runs/1'
WHEN = '2026-10-17T08:00:00Z'


def build(status='PASS', commit=SHA):
    return dict(status=status, checked_sha=commit, ci_url=URL, finished_at=WHEN, lean_version='Lean (fixture)', mathlib_commit='c' * 40, targets=['Carleman'])


def reviewed(row):
    row.update(verification_status='REVIEWED', lean_declarations=['Transfer.fixture'], declaration_version=SHA, build_evidence=build(), semantic_review=dict(checked_sha=SHA, declarations=['Transfer.fixture'], result='PASS', axiom_check='PASS', review_ref=URL, reviewed_at=WHEN))
    return row


class StatusRegression(unittest.TestCase):
    def setUp(self):
        self.x = json.loads((ROOT / 'state/progress.json').read_text())
        self.cov = json.loads((ROOT / 'state/paper_coverage.json').read_text())

    def test_initial_state_and_full_paper_coverage(self):
        dashboard.validate(self.x, self.cov)
        dashboard.validate_source(self.x, self.cov)
        self.assertEqual(len(self.x['claims']), 19)
        self.assertEqual(len(self.cov['results']), 26)
        self.assertEqual(sum(bool(r['claim_ids']) for r in self.cov['results']), 15)
        self.assertEqual(sum(dashboard.complete(c) for c in self.cov['results']), 0)

    def test_reviewed_conditional_is_never_original_complete(self):
        row = reviewed(self.x['claims'][3])
        dashboard.validate(self.x, self.cov)
        shown = dashboard.public_status(self.x, self.cov)['claims'][3]
        self.assertEqual(shown['scope'], 'CONDITIONAL')
        self.assertFalse(shown['paper_complete'])
        row['extra_hypotheses'] = []
        self.assertFalse(dashboard.complete(row))

    def test_original_completion_requires_no_extra_hypotheses(self):
        row = reviewed(self.cov['results'][0])
        dashboard.validate(self.x, self.cov)
        self.assertTrue(dashboard.complete(row))
        row['extra_hypotheses'] = ['Theorem 4.2 assumed']
        self.assertFalse(dashboard.complete(row))

    def test_stale_review_or_build_rejected(self):
        for field in ('semantic_review', 'build_evidence'):
            with self.subTest(field=field):
                x = copy.deepcopy(self.x)
                reviewed(x['claims'][3])[field]['checked_sha'] = OTHER
                with self.assertRaises(ValueError): dashboard.validate(x, self.cov)

    def test_unaudited_or_mismatched_declarations_rejected(self):
        row = reviewed(self.x['claims'][3])
        row['semantic_review']['declarations'] = ['Wrong.declaration']
        with self.assertRaises(ValueError): dashboard.validate(self.x, self.cov)
        row['semantic_review']['declarations'] = row['lean_declarations']
        row['semantic_review']['axiom_check'] = 'NOT_RUN'
        with self.assertRaises(ValueError): dashboard.validate(self.x, self.cov)

    def test_false_build_sha_and_missing_target_rejected(self):
        for field, value in [('checked_sha', 'test-evidence'), ('targets', []), ('mathlib_commit', 'main')]:
            with self.subTest(field=field):
                self.x['verification']['latest_build'] = build()
                self.x['verification']['latest_build'][field] = value
                with self.assertRaises(ValueError): dashboard.validate(self.x, self.cov)

    def test_missing_build_evidence_rejected(self):
        row = reviewed(self.x['claims'][3]); row['build_evidence'] = None
        with self.assertRaises(ValueError): dashboard.validate(self.x, self.cov)

    def test_projection_drops_nested_internal_metadata(self):
        marker = 'INTERNAL-NOTE-DO-NOT-PUBLISH'
        reviewed(self.x['claims'][3])
        def inject(obj):
            if isinstance(obj, dict):
                for child in list(obj.values()): inject(child)
                obj['internal_note'] = {'secret': marker}
            elif isinstance(obj, list):
                for child in obj: inject(child)
        inject(self.x); inject(self.cov)
        self.x['execution']['pause_reason'] = marker
        self.x['events'] = [{'at': WHEN, 'summary': marker, 'public_summary': '已保存检查点', 'internal_note': marker, 'url': URL}]
        serialized = json.dumps(dashboard.public_status(self.x, self.cov))
        self.assertNotIn(marker, serialized)
        self.assertNotIn(URL, serialized)
        self.assertNotIn('task_url', serialized)

    def test_unapproved_and_unsafe_links_hidden(self):
        self.x['verification']['latest_build'] = build()
        self.assertIsNone(dashboard.public_status(self.x, self.cov)['verification']['latest_build']['ci_url'])
        self.x['dashboard']['approved_urls'] = [URL]
        self.assertEqual(dashboard.public_status(self.x, self.cov)['verification']['latest_build']['ci_url'], URL)
        self.x['dashboard']['approved_urls'] = ['javascript:alert(1)']
        with self.assertRaises(ValueError): dashboard.validate(self.x, self.cov)

    def test_failure_keeps_last_successful_build(self):
        self.x['verification']['last_successful_build'] = build()
        newer = dashboard.overlay_ci(self.x, build('FAIL', OTHER), OTHER)
        self.assertEqual(newer['verification']['latest_build']['status'], 'FAIL')
        self.assertEqual(newer['verification']['latest_build']['checked_sha'], OTHER)
        self.assertEqual(newer['verification']['last_successful_build']['checked_sha'], SHA)
        self.assertIsNone(self.x['snapshot']['synced_at'])

    def test_ci_source_mismatch_rejected(self):
        with self.assertRaises(ValueError): dashboard.overlay_ci(self.x, build(), OTHER)

    def test_account_object_removed(self):
        self.assertNotIn('usage', dashboard.public_status(self.x, self.cov))
        self.x['usage'] = {}
        with self.assertRaises(ValueError): dashboard.validate(self.x, self.cov)

    def test_running_requires_a_real_task_record(self):
        self.x['execution']['state'] = 'RUNNING'
        with self.assertRaises(ValueError): dashboard.validate(self.x, self.cov)

    def test_task_base_and_state_must_match(self):
        task = dict(id='T001', platform_task_id='fixture', task_url=None, title='Fixture', goal_ids=['C001'], acceptance=['Build'], dependencies=[], branch='proof/fixture', base_commit=SHA, status='RUNNING', pr_url=None, checkpoint_commit=None, merge_commit=None, lean_declarations=[], build_evidence=None, blocker=None, attempts=[], next_action='Continue')
        self.x['tasks'] = [task]
        self.x['execution'].update(state='RUNNING', current_task_id='T001')
        dashboard.validate(self.x, self.cov)
        task['base_commit'] = 'unknown'
        with self.assertRaises(ValueError): dashboard.validate(self.x, self.cov)
        task['base_commit'] = SHA; task['status'] = 'REVIEW'
        with self.assertRaises(ValueError): dashboard.validate(self.x, self.cov)

    def test_unconfigured_or_empty_lean_project_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with self.assertRaisesRegex(ValueError, 'M0a incomplete'): validate_project(root)
            (root/'lean-toolchain').write_text('leanprover/lean4:v4.0.0')
            (root/'lakefile.toml').write_text('name="fixture"')
            (root/'lake-manifest.json').write_text(json.dumps({'packages':[{'name':'mathlib','rev':SHA}]}))
            (root/'Carleman.lean').write_text('import Mathlib\n')
            with self.assertRaisesRegex(ValueError, 'actual project proof'): validate_project(root)
            (root/'Carleman.lean').write_text('import Carleman.Periodic\n')
            self.assertEqual(validate_project(root), SHA)
            (root/'lean-toolchain').write_text('leanprover/lean4:stable')
            with self.assertRaisesRegex(ValueError, 'concrete Lean release'): validate_project(root)


if __name__ == '__main__': unittest.main()
