-- Prove2me | Theorems.Thm_Hirsch_parallel_displacements_force_affine_coordinate_levels
-- name    : Hirsch.parallel_displacements_force_affine_coordinate_levels
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-16T19:41:21.154769+00:00
-- url     : https://prove2.me/theorems/7ccd31e6-1b96-4c43-b1c4-f8c180eec7b8
-- title:
--   Distinct positive parallel displacements force a quadratic affine-coordinate level bound
-- statement:
--   Let V be a finite subset of any real vector space. Let p_i,q_i be points of V with q_i-p_i=lambda_i*g, where g is nonzero and the finitely indexed real lambda_i are positive and pairwise distinct. For every injective real linear map T into R^r and every translation offset, there exists an output coordinate j with (Tg)_j nonzero such that, writing K for the number of distinct values of (Tx)_j+offset_j on V, 2*card(I) <= K*(K-1). Thus the count is invariant under arbitrary injective affine embeddings, not just invertible square coordinate changes. The detecting coordinate is constructed using injectivity, not assumed. Empty pair families are permitted. No polytope structure or edge adjacency is required for this finite lemma. The Klee--Minty realization and exponential family size from the accompanying project research are not additional conclusions of this theorem. This is not a diameter lower bound or a proof of Polynomial Hirsch.
-- source:
--   Formalizes the finite parallel-length lemma in research/AFFINE_LEVEL_BARRIER.md (merged PR276). The proof injects forward and reversed scalar endpoint pairs into the off-diagonal of the finite coordinate image, using Mathlib Finset.offDiag_card. Classical finite counting; no historical-priority claim. This is distinct from accepted PR275 affine-angle conditioning.

import Mathlib
set_option autoImplicit false

theorem Hirsch.parallel_displacements_force_affine_coordinate_levels
    {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
    (V : Finset E) (p q : I → E) (g : E) (lambda : I → ℝ)
    (hp : ∀ i, p i ∈ V) (hq : ∀ i, q i ∈ V)
    (hg : g ≠ 0) (hpos : ∀ i, 0 < lambda i)
    (hinj : Function.Injective lambda)
    (hdisp : ∀ i, q i - p i = lambda i • g)
    (r : ℕ) (T : E →ₗ[ℝ] (Fin r → ℝ))
    (hT : Function.Injective T) (offset : Fin r → ℝ) :
    ∃ j : Fin r, (T g) j ≠ 0 ∧
      2 * Fintype.card I ≤
        (V.image (fun x => (T x) j + offset j)).card *
          ((V.image (fun x => (T x) j + offset j)).card - 1) := by sorry
