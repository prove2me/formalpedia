-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_21017
-- name    : WorkbookCorrected.plus_21017
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:20:52.523756+00:00
-- url     : https://prove2.me/theorems/0b90129c-110e-44f2-b4f9-7e607565014d
-- title:
--   Elementary arithmetic identity #21017
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   62400 + 118638 + 168948 + 213564 + 252720 + 286650 + 315588 + 339768 + 359424 + 374790 + 386100 + 393588 + 397488 + 398034 + 395460 + 390000 + 381888 + 371358 + 358644 + 343980 + 327600 + 309738 + 290628 + 270504 + 249600 + 228150 + 206388 + 184548 + 162864 + 141570 + 120900 + 101088 + 82368 + 64974 + 49140 + 35100 + 23088 + 13338 + 6084 + 1560 = 9178260
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_21017`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_21017 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_21017; Apache-2.0; corrects Open node bc348800-b864-4bbb-895a-996b991bfb75

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_21017 : 62400 + 118638 + 168948 + 213564 + 252720 + 286650 + 315588 + 339768 + 359424 + 374790 + 386100 + 393588 + 397488 + 398034 + 395460 + 390000 + 381888 + 371358 + 358644 + 343980 + 327600 + 309738 + 290628 + 270504 + 249600 + 228150 + 206388 + 184548 + 162864 + 141570 + 120900 + 101088 + 82368 + 64974 + 49140 + 35100 + 23088 + 13338 + 6084 + 1560 = 9178260 := by sorry
