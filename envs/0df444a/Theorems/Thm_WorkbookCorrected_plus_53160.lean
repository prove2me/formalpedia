-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_53160
-- name    : WorkbookCorrected.plus_53160
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:11:28.35073+00:00
-- url     : https://prove2.me/theorems/a971cff0-f925-4516-991b-a7d00c64710d
-- title:
--   Elementary arithmetic identity #53160
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 20 + 180 + 960 + 3360 + 8064 + 13440 + 15360 + 11520 + 5120 + 1024 = 59049
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_53160`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_53160 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_53160; Apache-2.0; corrects Open node 5ae0e72c-4e94-4d11-9065-568d6fd682b5

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_53160 : 1 + 20 + 180 + 960 + 3360 + 8064 + 13440 + 15360 + 11520 + 5120 + 1024 = 59049 := by sorry
