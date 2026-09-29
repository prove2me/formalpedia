-- Prove2me | Theorems.Thm_lean_workbook_plus_38628
-- name    : lean_workbook_plus_38628
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/eabefd88-9166-41e1-a3ac-735aa583d703
-- statement:
--   The maximal $k$ , for which the inequality $$\frac{a^3+b^3+c^3}{4abc}+\frac{1}{4}\ge\left(\frac{a^2+b^2+c^2}{ab+ac+bc}\right)^k$$ is true for any positives $a$ , $b$ and $c$ is $k=2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38628 : ∀ k : ℝ, (∀ a b c : ℝ, (a > 0 ∧ b > 0 ∧ c > 0 → (a^3 + b^3 + c^3) / (4 * a * b * c) + 1 / 4 ≥ (a^2 + b^2 + c^2) / (a * b + a * c + b * c)^k)) ↔ k ≤ 2   :=  by sorry
