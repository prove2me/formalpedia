-- Prove2me | Theorems.Thm_lean_workbook_plus_52544
-- name    : lean_workbook_plus_52544
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/e5d313e1-3782-4252-b1ee-9aa4bb3753ae
-- statement:
--   If A is a subring of B, and $b \in B$ is integral over A, show that there exists a monic polynomial with coefficients in A such that $b$ is a root of the polynomial. Also, show that there does not exist a non-monic polynomial with coefficients in A, where $a_0$ is not a unit, such that $b$ is a root of the polynomial.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52544 {A B : Type*} [CommRing A] [CommRing B]
  [Algebra A B] {b : B} (hb : b ∈ integralClosure A B) :
  ∃ p : Polynomial A, p.Monic ∧ p.eval₂ (algebraMap A B) b = 0  :=  by sorry
