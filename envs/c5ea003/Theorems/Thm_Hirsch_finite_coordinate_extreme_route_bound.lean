-- Prove2me | Theorems.Thm_Hirsch_finite_coordinate_extreme_route_bound
-- name    : Hirsch.finite_coordinate_extreme_route_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-16T23:46:20.103898+00:00
-- url     : https://prove2.me/theorems/1f61b140-7502-4508-a812-53fe712f2ad4
-- title:
--   Construct finite-face routes bounded by the actual coordinate-level inventory
-- statement:
--   Let a finite set of vertices carry a symmetric adjacency relation and separating real coordinate functions. Let a specified family of finite vertex subsets be closed under taking each nonempty coordinate minimum and maximum subset. In every family member, assume each vertex with another vertex of smaller (respectively larger) coordinate value has an adjacent vertex inside that member of strictly smaller (respectively larger) coordinate value. For any two vertices in any member F, construct an adjacency walk entirely inside F whose length is at most the sum over coordinates of the number of ACTUAL coordinate values on the whole finite vertex set minus one. No short route, bounded phase, connectivity or existing path is assumed. The proof ranks the real levels, constructs descent/ascent walks, chooses the cheaper joint extreme for both endpoints, and recursively assembles the walk. The conclusion is an explicit finite indexed sequence, not an algorithmic runtime claim. This is the finite-face construction underlying the Kleinschmidt--Onn coordinate-extreme argument. The structural local improvement and extreme-face closure assumptions remain explicit; this target does not itself instantiate them for arbitrary polytope edge graphs, prove the aggregate-cut coordinate closure from research #277, or establish a polynomial coordinate inventory for arbitrary carriers. It is not a proof of Polynomial Hirsch.
-- source:
--   Formal finite combinatorial interface for the coordinate-extreme argument used in research #274 and #277, especially research/CUT_VERTEX_LEVEL_CLOSURE.md Section 3. Classical context: Peter Kleinschmidt and Shmuel Onn, On the diameter of convex polytopes, Discrete Mathematics 102 (1992), 75-77, DOI 10.1016/0012-365X(92)90349-K; Alexander E. Black, Small Shadows of Lattice Polytopes, arXiv:2204.09129. No historical novelty claim. The public target uses Mathlib types only; internal Route is absent from its type.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.finite_coordinate_extreme_route_bound
    (n d : ℕ) (R : Fin n → Fin n → Prop)
    (hsym : ∀ a b, R a b → R b a)
    (c : Fin n → Fin d → ℝ) (hinj : Function.Injective c)
    (Face : Finset (Fin n) → Prop)
    (hminface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c a j ≤ c x j) → Face (F.filter (fun x => c x j = c a j)))
    (hmaxface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c x j ≤ c a j) → Face (F.filter (fun x => c x j = c a j)))
    (hdown : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c y j < c x j → ∃ z ∈ F, R x z ∧ c z j < c x j)
    (hup : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c x j < c y j → ∃ z ∈ F, R x z ∧ c x j < c z j)
    (F : Finset (Fin n)) (hF : Face F)
    (u v : Fin n) (hu : u ∈ F) (hv : v ∈ F) :
    ∃ L : ℕ, L ≤ ∑ j : Fin d,
        ((Finset.univ.image (fun x : Fin n => c x j)).card-1) ∧
      ∃ p : ℕ → Fin n, p 0 = u ∧ p L = v ∧
        (∀ i, i ≤ L → p i ∈ F) ∧ (∀ i, i < L → R (p i) (p (i+1))) := by sorry
