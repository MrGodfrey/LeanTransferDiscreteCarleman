"""Regression cases for the review's concrete failure modes. Fixtures are synthetic."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import update_dashboard as dashboard
from validate_lean_project import validate_project

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = Path(__file__).resolve().parent / 'fixtures'
SHA = 'a' * 40
OTHER = 'b' * 40
URL = 'https://github.com/example/project/actions/runs/1'
WHEN = '2026-10-17T08:00:00Z'


def build(status='PASS', commit=SHA):
    return dict(status=status, checked_sha=commit, ci_url=URL, finished_at=WHEN, lean_version='Lean (fixture)', mathlib_commit='c' * 40, targets=['Carleman'])


def reviewed(row):
    row.update(verification_status='REVIEWED', lean_declarations=['Transfer.fixture'], declaration_version=SHA, build_evidence=build(), semantic_review=dict(checked_sha=SHA, declarations=['Transfer.fixture'], result='PASS', axiom_check='PASS', review_ref=URL, reviewed_at=WHEN))
    return row


def local_build():
    return {**build(), 'source': 'local', 'ci_url': None,
            'source_manifest_sha256': 'd' * 64,
            'commands': [{'command': 'lake build Carleman', 'exit_code': 0},
                         {'command': 'lake env lean tools/CheckAxioms.lean', 'exit_code': 0}],
            'axiom_audit': {'status': 'PASS', 'declarations': 12, 'sha256': 'e' * 64}}


class StatusRegression(unittest.TestCase):
    def setUp(self):
        # Frozen inputs, never the live project ledger: progress is allowed.
        self.x = json.loads((FIXTURES / 'initial_progress.json').read_text())
        self.cov = json.loads((FIXTURES / 'initial_paper_coverage.json').read_text())

    def test_initial_state_and_full_paper_coverage(self):
        dashboard.validate(self.x, self.cov)
        self.assertEqual(len(self.x['claims']), 19)
        self.assertEqual(len(self.cov['results']), 26)
        self.assertEqual(sum(bool(r['claim_ids']) for r in self.cov['results']), 15)
        self.assertEqual(sum(dashboard.complete(c) for c in self.cov['results']), 0)

    def test_progress_can_add_claims_complete_results_and_run_tasks(self):
        row = copy.deepcopy(self.x['claims'][0])
        row.update(id='AUX001', title='Additional auxiliary result')
        self.x['claims'].append(reviewed(row))
        reviewed(self.cov['results'][0])
        task = dict(id='T001', platform_task_id='fixture', task_url=None,
                    title='Next task', goal_ids=['AUX001'], acceptance=['Build'],
                    dependencies=[], branch='proof/next', base_commit=SHA,
                    status='RUNNING', pr_url=None, checkpoint_commit=None,
                    merge_commit=None, lean_declarations=[], build_evidence=None,
                    blocker=None, attempts=[], next_action='Continue')
        self.x['tasks'] = [task]
        self.x['execution'].update(state='RUNNING', current_task_id='T001')
        self.x['snapshot']['synced_at'] = WHEN
        dashboard.validate(self.x, self.cov)
        shown = dashboard.public_status(self.x, self.cov)
        self.assertEqual(len(shown['claims']), 20)
        self.assertEqual(sum(c['paper_complete'] for c in shown['coverage']), 1)
        self.assertFalse(shown['claims'][-1]['paper_complete'])
        self.assertEqual(shown['execution']['state'], 'RUNNING')

    def test_reviewed_conditional_is_never_original_complete(self):
        row = reviewed(self.x['claims'][3])
        dashboard.validate(self.x, self.cov)
        shown = dashboard.public_status(self.x, self.cov)['claims'][3]
        self.assertEqual(shown['scope'], 'CONDITIONAL')
        self.assertFalse(shown['paper_complete'])
        row['extra_hypotheses'] = []
        self.assertFalse(dashboard.complete(row))

    def test_direct_main_integration_without_pr_keeps_commit_requirement(self):
        task = dict(id='T001', platform_task_id='fixture', task_url=None,
                    title='Local stage', goal_ids=[], acceptance=['Build'],
                    dependencies=[], branch='main', base_commit=SHA,
                    status='MERGED', integration_mode='direct-main', pr_url=None,
                    checkpoint_commit=OTHER, merge_commit=OTHER, lean_declarations=[],
                    build_evidence=None, blocker=None, attempts=[], next_action='Continue')
        self.x['tasks'] = [task]
        dashboard.validate(self.x, self.cov)
        for field, value in [('merge_commit', None), ('branch', 'proof/fixture'),
                             ('integration_mode', None)]:
            with self.subTest(field=field):
                x = copy.deepcopy(self.x)
                x['tasks'][0][field] = value
                with self.assertRaises(ValueError): dashboard.validate(x, self.cov)

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

    def test_exact_local_build_can_support_independent_review_without_remote_ci(self):
        row = reviewed(self.x['claims'][3])
        row['build_evidence'] = local_build()
        dashboard.validate(self.x, self.cov)
        shown = dashboard.public_status(self.x, self.cov)['claims'][3]['build_evidence']
        self.assertEqual(shown['source'], 'local')
        self.assertIsNone(shown['ci_url'])
        self.assertNotIn('commands', shown)
        row['build_evidence']['checked_sha'] = OTHER
        with self.assertRaises(ValueError): dashboard.validate(self.x, self.cov)

    def test_local_pass_requires_successful_commands_source_and_axiom_evidence(self):
        cases = [('commands', []), ('commands', [{'command': 'lake build', 'exit_code': 1}]),
                 ('commands', [{'command': 'lake build', 'exit_code': False}]),
                 ('source_manifest_sha256', None), ('axiom_audit', None),
                 ('axiom_audit', {'status': 'FAIL', 'declarations': 12, 'sha256': 'e' * 64}),
                 ('ci_url', URL)]
        for field, value in cases:
            with self.subTest(field=field, value=value):
                b = local_build(); b[field] = value
                with self.assertRaises(ValueError): dashboard.validate_build(b)

    def test_local_evidence_cannot_masquerade_as_a_remote_snapshot(self):
        with self.assertRaises(ValueError): dashboard.overlay_ci(self.x, local_build(), SHA)

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

    def test_current_run_url_displayed_without_changing_source_or_task_freshness(self):
        self.x['project']['repository_url'] = 'https://github.com/example/project'
        url = self.x['project']['repository_url'] + '/actions/runs/123/attempts/2'
        result = build(); result['ci_url'] = url
        before = copy.deepcopy(self.x)
        newer = dashboard.overlay_ci(self.x, result, SHA, url)
        shown = dashboard.public_status(newer, self.cov)
        self.assertEqual(shown['verification']['latest_build']['ci_url'], url)
        self.assertEqual(newer['execution'], before['execution'])
        self.assertEqual(self.x, before)
        self.assertEqual(newer['snapshot']['source_commit'], SHA)
        self.assertEqual(newer['snapshot']['mode'], 'CI_SNAPSHOT')
        self.assertEqual(newer['dashboard']['approved_urls'], before['dashboard']['approved_urls'] + [url])

    def test_ci_run_mismatch_and_unrelated_urls_rejected(self):
        self.x['project']['repository_url'] = 'https://github.com/example/project'
        prefix = self.x['project']['repository_url'] + '/actions/runs/'
        for url in [prefix + '123/attempts/1', URL, prefix + '123/attempts/1?redirect=1',
                    prefix + '../issues/1', prefix + '123/attempts/0']:
            with self.subTest(url=url):
                result = build(); result['ci_url'] = prefix + '124/attempts/1'
                with self.assertRaises(ValueError): dashboard.overlay_ci(self.x, result, SHA, url)

    def test_result_url_cannot_approve_itself(self):
        result = build()
        newer = dashboard.overlay_ci(self.x, result, SHA)
        self.assertIsNone(dashboard.public_status(newer, self.cov)['verification']['latest_build']['ci_url'])
        self.assertEqual(newer['dashboard']['approved_urls'], self.x['dashboard']['approved_urls'])

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


class CurrentStateValidation(unittest.TestCase):
    def test_live_records_match_the_actual_manuscript(self):
        x = json.loads((ROOT / 'state/progress.json').read_text())
        coverage = json.loads((ROOT / 'state/paper_coverage.json').read_text())
        dashboard.validate(x, coverage)
        dashboard.validate_source(x, coverage)


if __name__ == '__main__': unittest.main()
