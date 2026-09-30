-- Prove2me | Theorems.Thm_Hirsch_parallel_support_bridge_uniform_endpoint_exposers
-- name    : Hirsch.parallel_support_bridge_uniform_endpoint_exposers
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T15:18:56.513831+00:00
-- url     : https://prove2.me/theorems/0918de00-86f9-4f1d-9e20-7d1dc36efa69
-- title:
--   Construct uniform two-sided strict endpoint objectives for a parallel Minkowski bridge
-- statement:
--   Let S_i be finitely many finite point sets in a real vector space. Suppose a common linear functional f exposes, in each factor, the segment with listed endpoints a_i,b_i, where b_i=a_i+eta_i e, eta_i>=0, and e is nonzero with f(e)=0. It suffices to provide the finite upper bounds and to require every maximizing listed point to lie in that segment. Then there exist a linear functional q with q(e)=1 and one positive number delta such that for EVERY 0<s<delta, f-sq strictly exposes a_i among the points of S_i and f+sq strictly exposes b_i, simultaneously for all i. These functionals also uniquely expose sum_i a_i and sum_i b_i on the WHOLE Minkowski sum of the convex hulls, and both endpoints belong to that sum. The endpoint functionals and their common radius are conclusions, not additional exposure witnesses. The same given bridge endpoints are retained. Point factors, redundant interior points, empty factor families and lower-dimensional factors are allowed. The result supplies the strict endpoint-objective compatibility needed to connect the accepted core-edge bridge (#240) to the constructed fixed-core fibre paths (#244). It does not construct an arbitrary core edge or prove a uniform Polynomial Hirsch diameter bound.
-- source:
--   Classical finite lexicographic perturbation and Minkowski support geometry. Primary context: Antoine Deza and Lionel Pournin, Diameter, decomposability, and Minkowski sums of polytopes, arXiv:1806.07643v1, Section 2 and Lemma 3.8; https://arxiv.org/html/1806.07643v1. The normalized dual-coordinate and convex-hull support arguments adapt accepted project packet generic_minkowski_edge_lift/solution.lean, Git blob884daa33d3890f6d45b8adf8d967aa27eac8f09a. The new formal interface constructs a single two-sided perturbation radius and binds strict component and whole-sum endpoints to the same supporting bridge. No historical novelty claim.

import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.parallel_support_bridge_uniform_endpoint_exposers
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (S : Fin m → Finset E)
    (a b : Fin m → E) (η : Fin m → ℝ) (e : E)
    (he : e ≠ 0) (f : E →ₗ[ℝ] ℝ) (hf : f e = 0)
    (ha : ∀ i, a i ∈ S i) (hb : ∀ i, b i ∈ S i)
    (hη : ∀ i, 0 ≤ η i) (hba : ∀ i, b i = a i+η i • e)
    (hbound : ∀ i x, x ∈ S i → f x ≤ f (a i))
    (hface : ∀ i x, x ∈ S i → f x = f (a i) → x ∈ segment ℝ (a i) (b i)) :
    let R : Set E := {z | ∃ x : Fin m → E,
      (∀ i, x i ∈ convexHull ℝ (S i : Set E)) ∧ (∑ i, x i) = z}
    ∃ (q : E →ₗ[ℝ] ℝ) (δ : ℝ), q e = 1 ∧ 0 < δ ∧
      (∑ i, a i) ∈ R ∧ (∑ i, b i) ∈ R ∧
      ∀ s : ℝ, 0 < s → s < δ →
        (∀ i x, x ∈ S i → x ≠ a i → (f-s • q) x < (f-s • q) (a i)) ∧
        (∀ i x, x ∈ S i → x ≠ b i → (f+s • q) x < (f+s • q) (b i)) ∧
        (∀ z ∈ R, (f-s • q) z ≤ (f-s • q) (∑ i, a i) ∧
          ((f-s • q) z = (f-s • q) (∑ i, a i) → z = ∑ i, a i)) ∧
        (∀ z ∈ R, (f+s • q) z ≤ (f+s • q) (∑ i, b i) ∧
          ((f+s • q) z = (f+s • q) (∑ i, b i) → z = ∑ i, b i)) := by sorry
