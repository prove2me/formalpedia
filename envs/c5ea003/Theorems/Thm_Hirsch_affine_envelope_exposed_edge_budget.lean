-- Prove2me | Theorems.Thm_Hirsch_affine_envelope_exposed_edge_budget
-- name    : Hirsch.affine_envelope_exposed_edge_budget
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T01:01:09.060715+00:00
-- url     : https://prove2.me/theorems/98b9fed3-829a-49fe-b099-e46f0f2b08a8
-- title:
--   Additive factor-state budget for certified simultaneous exposed-edge sweeps
-- statement:
--   Let R be a subset of a real vector space, and choose a fixed offset o and finitely many finite point dictionaries v_i with k_i entries. At increasing sample times, choose the unique maximizer from each dictionary for one affine family of linear objectives f_0+t f_1. Form the sum of the chosen points plus o. Suppose each consecutive summed point differs, and a supplied global supporting functional exposes exactly the segment joining that pair in R. Then these segments form a genuine ordinary-edge route of length N, with
--
--   $$N\le\sum_i(k_i-1).$$
--
--   No no-revisiting, rank-budget, or desired length bound is a supplied hypothesis. A change of affine maximizer strictly increases its slope, which supplies the additive state budget. Simultaneous changes are permitted only when their global support certificate is an exposed segment; a higher-dimensional face does not qualify.
--
--   This is a finite certificate theorem, not an existence theorem for arbitrary R or arbitrary requested endpoints. In a Minkowski fibre sweep, o is a fixed core vertex and each dictionary is the finite vertex list of a summand; the existing supporting-face identities construct the global certificates. The accompanying mathematical argument gives a core-path lift bound L+(L+1)sum_i(k_i-1). That full normal-fan existence argument is not part of this Lean target. For N=0 the route conclusion has no edge obligations and does not assert endpoint membership in R; for N>0 the exposed-segment certificates provide the actual endpoints and edges.
-- source:
--   Classical affine-envelope monotonicity; Deza and Pournin, Diameter, decomposability, and Minkowski sums of polytopes, arXiv:1806.07643v1, pp. 9-11, Lemmas 3.7-3.8 and Theorem 3.5 (one-summand fibre lifting). The simultaneous summed-envelope extension, proof and exact implementation are in research/SIMULTANEOUS_MINKOWSKI_LIFT.md. Supporting-extreme proof reuses the argument in Solutions/PolynomialMinkowskiExposedEdges.lean at Git blob bb3cc16aec0ca7a521354dc7785c17a5cfbda9f3. No historical novelty claim.

import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.affine_envelope_exposed_edge_budget
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (R : Set E) (o : E) (r N : ℕ) (k : Fin r → ℕ)
    (v : (i : Fin r) → Fin (k i) → E)
    (f0 f1 : E →ₗ[ℝ] ℝ)
    (pick : ℕ → (i : Fin r) → Fin (k i)) (time : ℕ → ℝ)
    (wall : ℕ → E →ₗ[ℝ] ℝ) (cap : ℕ → ℝ)
    (hinc : ∀ j, j < N → time j < time (j+1))
    (hmax : ∀ j, j ≤ N → ∀ i q, q ≠ pick j i →
      f0 (v i q) + time j*f1 (v i q) <
        f0 (v i (pick j i)) + time j*f1 (v i (pick j i)))
    (hne : ∀ j, j < N →
      o + (∑ i, v i (pick j i)) ≠ o + (∑ i, v i (pick (j+1) i)))
    (hbound : ∀ j, j < N → ∀ z ∈ R, wall j z ≤ cap j)
    (hface : ∀ j, j < N →
      {z | z ∈ R ∧ wall j z = cap j} =
        segment ℝ (o + (∑ i, v i (pick j i)))
          (o + (∑ i, v i (pick (j+1) i)))) :
    N ≤ ∑ i, (k i - 1) ∧
      ∃ p : ℕ → E,
        p 0 = o + (∑ i, v i (pick 0 i)) ∧
        p N = o + (∑ i, v i (pick N i)) ∧
        ∀ j, j < N → p j ≠ p (j+1) ∧
          IsExtreme ℝ R (segment ℝ (p j) (p (j+1))) := by sorry
