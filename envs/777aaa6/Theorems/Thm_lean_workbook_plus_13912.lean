-- Prove2me | Theorems.Thm_lean_workbook_plus_13912
-- name    : lean_workbook_plus_13912
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/3d6cc570-df7f-46fd-992d-0fae64aff9f5
-- statement:
--   If $(a,b)=(a,c)=1$ for some integers $a,b,c$ (distinct than $0$ ) and for $\forall m \in \mathbb{N}$ we have $a^{m}|b^{m}-c^{m}$ prove that $a=\pm 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13912 (a b c : ℤ) (h1 : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (h2 : (a, b) = 1 ∧ (a, c) = 1) (h3 : ∀ m : ℕ, a ^ m ∣ b ^ m - c ^ m) : a = 1 ∨ a = -1   :=  by sorry
