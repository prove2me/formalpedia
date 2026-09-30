-- Prove2me | Theorems.Thm_Hirsch_cut_vertex_positive_support_certificate
-- name    : Hirsch.cut_vertex_positive_support_certificate
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T10:02:27.424763+00:00
-- url     : https://prove2.me/theorems/1043e661-f761-4ee3-9d75-2822a58c77f9
-- title:
--   Construct positive cut-vertex supports and uniquely recover their weights from active cuts
-- statement:
--   For any set S in a finite-dimensional real coordinate space and any finite family of linear halfspaces, every extreme point x of their intersection with convexHull(S) admits a finite strictly positive convex representation using points of S. The selected homogenized support vectors are linearly independent, and so are their images under the actual cuts active at x. The support has at most d+1 points and at most number-of-active-cuts+1 points. Given this selected support, its real weights are uniquely determined by having total one and the original right-hand-side values on all active cuts; even signed alternative weights satisfying those equations coincide with the constructed positive weights. Neither a support list, weights, affine independence, active-image injectivity, rank oracle nor a support-cardinality bound is supplied. S need not be finite or compact. Support points need not satisfy the cuts individually. Uniqueness is for weights on the selected support, not a claim that the support itself is canonical or unique. This theorem does not extract a minimal independent active-row subsystem, bound a full coordinate alphabet for arbitrary carriers, certify a runtime support-finding algorithm, or prove Polynomial Hirsch.
-- source:
--   Composition of pinned Mathlib eq_pos_convex_span_of_mem_convexHull (Caratheodory) with the complete accepted helper proof namespace from PR #290, Hirsch.cut_vertex_active_support_injectivity, theorem c3781e27-7eb2-4ffc-bb5b-e85ffe60c480. The accepted namespace prefix is reused byte-for-byte; its old public solution and axiom-print suffix are not repeated. Source solution blob56e38bebb4d5b3501ee47c05df59631d5c5c0543, SHA2563dd3f72bd43461fc68baadd0e12b0dad7526c0cedeece628ca9cdf256b1dd499. New proof reindexes the actually selected positive support to Fin n, proves homogenized independence, applies actual extremality, obtains both cardinal bounds, and proves real-weight uniqueness. Classical convex geometry; no historical novelty claim. This is the next concrete support-selection step toward the written #277 cut-image alphabet interface.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.cut_vertex_positive_support_certificate
    (m d : ℕ) (S : Set (Fin d → ℝ))
    (C : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (x : Fin d → ℝ)
    (hx : x ∈ (convexHull ℝ S ∩ {y | ∀ j, C j y ≤ b j}).extremePoints ℝ) :
    ∃ (n : ℕ) (v : Fin n → Fin d → ℝ) (w : Fin n → ℝ),
      (∀ i, v i ∈ S) ∧ (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      (∑ i, w i • v i) = x ∧
      LinearIndependent ℝ (fun i => ((1 : ℝ), v i)) ∧
      LinearIndependent ℝ
        (fun i => ((1 : ℝ), fun j : {j : Fin m // C j x = b j} => C j.val (v i))) ∧
      n ≤ d + 1 ∧ n ≤ Nat.card {j : Fin m // C j x = b j} + 1 ∧
      (∀ u : Fin n → ℝ, (∑ i, u i) = 1 →
        (∀ j, C j x = b j → (∑ i, u i * C j (v i)) = b j) → u = w) := by sorry
