-- Prove2me | Theorems.Thm_lean_workbook_plus_37982
-- name    : lean_workbook_plus_37982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/145f6993-cfd0-4dff-a8ab-60c772c343fe
-- statement:
--   If $\gcd(a,b) =1$, $e \mid ac$ and $e \mid bc$, then prove that $e \mid c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37982 (a b c e : ℕ) (h1 : Nat.Coprime a b) (h2 : e ∣ a*c) (h3 : e ∣ b*c) : e ∣ c   :=  by sorry
