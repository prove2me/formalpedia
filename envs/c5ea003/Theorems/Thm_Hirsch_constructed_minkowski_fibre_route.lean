-- Prove2me | Theorems.Thm_Hirsch_constructed_minkowski_fibre_route
-- name    : Hirsch.constructed_minkowski_fibre_route
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T04:34:30.473397+00:00
-- url     : https://prove2.me/theorems/2f4c0ca7-8412-47e8-8ab6-4d44b8699ee5
-- title:
--   Construct actual Minkowski fibre edges with additive factor cost and no core-size charge
-- statement:
--   Let P be the convex hull of a finite core point list and Q the Minkowski sum of finitely and injectively listed factor hulls S_i. Given two endpoint tuples and objectives strictly exposing their respective factor choices and the SAME core point, construct a path between the summed endpoints in P+Q with at most sum_i(k_i-1) ordinary edges. Every path point belongs to P+Q, including the zero-step case. Every transition is a nondegenerate entire exposed segment of the FULL sum, not merely an edge of Q or an auxiliary graph. There is NO charge for the number of core points. Generic perturbation, event ordering, interval winners, common wall maxima, stationary compression, noncancellation, and the route are derived. The proof reuses the verified scalar sequence of #243; it does not register another scalar theorem. Finite presentations and strict exposed endpoint tuples are inputs; arbitrary-carrier decomposition, core-bridge concatenation, and a dimension-uniform facet-count bound are not conclusions.
-- source:
--   Classical finite Minkowski/normal-fan fibre geometry. Reuses verified #243 scalar crossing sequence (source c26a8737a7d2b3c697b9b5a197f0733b3129f2ad60b16071adb6f15e3a5ec8dc), accepted #242 generic objectives, #239 slope-rank count and compiled whole-crossing support geometry. New proof instantiates these data on the actual points, preserves strict core comparisons, and proves whole-sum supporting slices and actual route existence. Related primary reference: Deza--Pournin arXiv:1806.07643v1. Not a new classical diameter theorem or Polynomial Hirsch solution.

import Mathlib
open Set
open scoped BigOperators

namespace Hirsch
theorem constructed_minkowski_fibre_route
    {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]
    (a r : ℕ) (core : Fin a → E) (o : Fin a) (k : Fin r → ℕ)
    (v : (i : Fin r) → Fin (k i) → E) (hinj : ∀ i, Function.Injective (v i))
    (p0 p1 : (i : Fin r) → Fin (k i)) (f0 g0 : E →ₗ[ℝ] ℝ)
    (hc0 : ∀ q, q≠o → f0 (core q)<f0 (core o))
    (hc1 : ∀ q, q≠o → g0 (core q)<g0 (core o))
    (hp0 : ∀ i q, q≠p0 i → f0 (v i q)<f0 (v i (p0 i)))
    (hp1 : ∀ i q, q≠p1 i → g0 (v i q)<g0 (v i (p1 i))) :
    let P : Set E := convexHull ℝ ((Finset.univ.image core : Finset E) : Set E)
    let Q : Set E := {z | ∃ x : Fin r → E,
      (∀ i, x i ∈ convexHull ℝ ((Finset.univ.image (v i) : Finset E) : Set E)) ∧
      (∑ i, x i)=z}
    let R : Set E := {z | ∃ x∈P, ∃ y∈Q, x+y=z}
    ∃ N : ℕ, N≤∑ i, (k i-1) ∧ ∃ path : ℕ → E,
      path 0=core o+∑ i, v i (p0 i) ∧ path N=core o+∑ i, v i (p1 i) ∧
      (∀ j, j≤N → path j∈R) ∧
      (∀ j, j≤N → ∃ z∈Q, path j=core o+z) ∧
      ∀ j, j<N →
        (∃ h : E →ₗ[ℝ] ℝ, (∀ z∈R, h z≤h (path j)) ∧
          {z | z∈R ∧ h z=h (path j)}=segment ℝ (path j) (path (j+1))) ∧
        path j≠path (j+1) ∧ IsExtreme ℝ R (segment ℝ (path j) (path (j+1))) := by sorry
end Hirsch
