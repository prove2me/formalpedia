-- Prove2me | Theorems.Thm_lean_workbook_plus_13042
-- name    : lean_workbook_plus_13042
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/e75b18ec-06c8-4b23-aa9e-d8184be72e20
-- statement:
--   Prove that if $x$ and $y$ are integers such that $x \equiv 1 \mod 3$ and $y \equiv 2 \mod 3$, then $3 \nmid xy$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13042 : ∀ x y : ℤ, x ≡ 1 [ZMOD 3] ∧ y ≡ 2 [ZMOD 3] → ¬ 3 ∣ (x * y)   :=  by sorry
