-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_48564
-- name    : WorkbookCorrected.plus_48564
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:27.199913+00:00
-- url     : https://prove2.me/theorems/87001862-28d7-4f58-8bc3-f5399c36d6ea
-- title:
--   Ten factorial over two and eight factorial
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \frac{10!}{2!\,8!} = 45
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_48564`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_48564 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_48564; Apache-2.0; corrects Open node 2734dbc5-8bd6-4bdb-8214-68e76922be31

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_48564 : Nat.factorial 10 / (Nat.factorial 2 * Nat.factorial 8) = 45 := by sorry
