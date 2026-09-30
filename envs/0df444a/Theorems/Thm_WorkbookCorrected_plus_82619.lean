-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_82619
-- name    : WorkbookCorrected.plus_82619
-- status  : Disproved
-- author  : @carlok
-- created : 2026-09-30T09:39:42.294998+00:00
-- url     : https://prove2.me/theorems/f88db1bf-ed16-44ef-bfc5-8e83226d4ef9
-- title:
--   Elementary arithmetic identity #82619
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   2 + 12 + 30 + 56 + 90 + 132 + 182 + 240 + 306 + 380 + 462 + 552 + 650 + 756 + 870 + 992 + 1122 + 1260 + 1406 + 1560 + 1722 + 1892 + 2070 + 2256 + 2450 + 2652 + 2862 + 3080 + 3306 + 3540 + 3782 + 4032 + 4290 + 4556 + 4830 + 5112 + 5402 + 5700 + 6006 + 6320 + 6642 + 6972 + 7310 + 7656 + 8010 + 8372 + 8742 + 9120 + 9506 + 9900 = 24500
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_82619`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_82619 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_82619; Apache-2.0; corrects Open node 621c9aeb-6d14-4f80-80a2-f1b7ba5b04f4

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_82619 : 2 + 12 + 30 + 56 + 90 + 132 + 182 + 240 + 306 + 380 + 462 + 552 + 650 + 756 + 870 + 992 + 1122 + 1260 + 1406 + 1560 + 1722 + 1892 + 2070 + 2256 + 2450 + 2652 + 2862 + 3080 + 3306 + 3540 + 3782 + 4032 + 4290 + 4556 + 4830 + 5112 + 5402 + 5700 + 6006 + 6320 + 6642 + 6972 + 7310 + 7656 + 8010 + 8372 + 8742 + 9120 + 9506 + 9900 = 24500 := by sorry
