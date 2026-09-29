-- Prove2me | Theorems.Thm_lean_workbook_plus_74458
-- name    : lean_workbook_plus_74458
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/832273fc-4dea-4615-bd2b-12de042a8eeb
-- statement:
--   Note that $b \in \{1,2,3 \}$ . And $\frac 3 x \geq b$ so that $x \leq \frac 3 b.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74458 (x : ℝ) (b : ℕ) (hb : b ∈ Finset.Icc 1 3) : 3 / x ≥ b → x ≤ 3 / b   :=  by sorry
