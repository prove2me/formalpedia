-- Prove2me | Theorems.Thm_Hirsch_moment_six_row_no_uniform_local_contraction
-- name    : Hirsch.moment_six_row_no_uniform_local_contraction
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-18T20:33:24.304261+00:00
-- url     : https://prove2.me/theorems/9771bc05-8eb9-4606-a21e-79715873624e
-- title:
--   All incident moment-polytope edge gains can be arbitrarily small while three edges suffice
-- statement:
--   For every positive real delta, construct e with 0<e<1/4 and the explicit mean-centered two-dimensional moment system on six nodes (-1,0,e,2e,3e,1). The explicit source u, target v, and two named neighbors l,r are actual Mathlib extreme points. The target score is the sum of the ORIGINAL rows labelled 0 and 5, which are exactly the target tight rows. The exposed nondegenerate original-segment neighbors of u are EXACTLY l and r. EVERY such neighbor makes a strictly positive score gain smaller than delta times the full source-to-target gap. Nevertheless construct a route with exactly three nondegenerate exposed ORIGINAL edges from u to v. No feasible point, neighbor list, rank certificate, small-gain premise, edge oracle or path is assumed. Completeness of the two-neighbor list is proved using the exposing functional and explicit source-cone decomposition, not merely checked by enumeration. The claim rules out a coefficient-independent positive fractional improvement bound for this fixed local target score even at d=2,m=6. It does not assert a long path, a diameter lower bound, failure of a polynomial routing policy, formal shortestness of the supplied route, or Polynomial Hirsch.
-- source:
--   Continues accepted #303 Hirsch.moment_quantitative_neighbor_transport and its written five-row mass limitation. That example had a substantial best actual gain; this new six-node family makes both actual gains small, with an explicit three-edge route. Reuses the exact 544-line namespace prefix through Hirsch.MomentEdges from the accepted source blob6d3b107ba24b08e9562ab8c132a093274f823a9d, without old public targets. Related fixed-type radial/angular contraction obstructions in project research #256 are acknowledged; no first historical obstruction claim. Distinct from owned #300 separated-pair routes and #302 even-gap catalogue.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_six_row_no_uniform_local_contraction (δ : ℝ) (hδ : 0 < δ) :
    ∃ e : ℝ, 0 < e ∧ e < 1/4 ∧
      let a : Fin 6 → ℝ := ![-1,0,e,2*e,3*e,1]
      let u : Fin 2 → ℝ := ![9*e/(1+4*e^2),-3/(1+4*e^2)]
      let l : Fin 2 → ℝ := ![3*e/(1+4*e^2),-3/(1+4*e^2)]
      let r : Fin 2 → ℝ := ![15*e/(1+10*e^2),-3/(1+10*e^2)]
      let v : Fin 2 → ℝ := ![0,3/(2-7*e^2)]
      let A : (Fin 2 → ℝ) → Fin 6 → ℝ := fun x i =>
        ∑ j : Fin 2, (a i ^ (j.val+1) - (∑ k, a k ^ (j.val+1))/(6 : ℝ))*x j
      let P : Set (Fin 2 → ℝ) := {x | ∀ i, A x i ≤ 1}
      let f : (Fin 2 → ℝ) → ℝ := fun x => A x 0 + A x 5
      u ∈ P.extremePoints ℝ ∧ v ∈ P.extremePoints ℝ ∧ u ≠ v ∧
      0 < f v-f u ∧ l ≠ r ∧
      (∀ z : Fin 2 → ℝ,
        (z ∈ P.extremePoints ℝ ∧ z ≠ u ∧ IsExposed ℝ P (segment ℝ u z)) ↔ z=l ∨ z=r) ∧
      (∀ z : Fin 2 → ℝ,
        (z ∈ P.extremePoints ℝ ∧ z ≠ u ∧ IsExposed ℝ P (segment ℝ u z)) →
          0 < f z-f u ∧ f z-f u < δ*(f v-f u)) ∧
      ∃ path : Fin 4 → (Fin 2 → ℝ), path 0=u ∧ path 3=v ∧
        (∀ i, path i ∈ P.extremePoints ℝ) ∧
        ∀ i : Fin 3, path i.castSucc ≠ path i.succ ∧
          IsExposed ℝ P (segment ℝ (path i.castSucc) (path i.succ)) := by sorry
