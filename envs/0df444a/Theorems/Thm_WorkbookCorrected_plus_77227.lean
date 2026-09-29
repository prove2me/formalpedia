-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_77227
-- name    : WorkbookCorrected.plus_77227
-- status  : Disproved
-- author  : @carlok
-- created : 2026-09-22T11:56:32.96826+00:00
-- url     : https://prove2.me/theorems/fac498ce-8685-47fb-9a98-a88cf1ebe3ef
-- title:
--   Factorial arithmetic identity #77227
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (6!)/(2!*2!) = 90
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_77227`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_77227 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_77227; Apache-2.0; corrects Open node 927c9b63-9619-4286-ae1a-e7afd755e336

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_77227 : (Nat.factorial 6)/((Nat.factorial 2)*(Nat.factorial 2)) = 90 := by sorry
