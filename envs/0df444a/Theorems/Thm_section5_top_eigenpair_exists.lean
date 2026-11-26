-- Prove2me | Theorems.Thm_section5_top_eigenpair_exists
-- name    : section5_top_eigenpair_exists
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:35.815008+00:00
-- url     : https://prove2.me/theorems/abb175c0-4e4b-40d0-a5e3-b96914ace8d1
-- title:
--   Existence of a unit top eigenvector for a self-adjoint operator
-- statement:
--   Let E be a nontrivial finite-dimensional complex inner-product space and L a self-adjoint bounded complex-linear operator. There exist a unit v∈E and real λ such that $$Lv=\lambda v,\qquad\forall x\in E,\ \|x\|=1\implies\operatorname{Re}\langle x,Lx\rangle\le\lambda.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5SpectralDeflation.lean, lines 145–149.

import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_top_eigenpair_exists {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (L : E →L[ℂ] E) (hL : IsSelfAdjoint L) :
    ∃ (v : E) (lam : ℝ), ‖v‖=1 ∧ L v=(lam:ℂ) • v ∧
      ∀ x : E, ‖x‖=1 → (inner ℂ x (L x)).re ≤ lam := by sorry
