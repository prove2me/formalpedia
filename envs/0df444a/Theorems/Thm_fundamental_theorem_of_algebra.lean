-- Prove2me | Theorems.Thm_fundamental_theorem_of_algebra
-- name    : fundamental_theorem_of_algebra
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-05-22T13:56:19.510023+00:00
-- url     : https://prove2.me/theorems/a8cca507-0acb-4709-9b2c-c836523b0c0d
-- statement:
--   Every nonconstant polynomial with complex coefficients has at least one complex root. Equivalently, for every complex polynomial $f$ with positive degree, there exists $z \in \mathbb{C}$ such that $f(z)=0$.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Mathlib.Analysis.Complex.Polynomial.Basic

theorem fundamental_theorem_of_algebra (f : Polynomial ℂ) (hf : 0 < f.degree) : ∃ z : ℂ, f.IsRoot z := by sorry
