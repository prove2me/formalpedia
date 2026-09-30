-- Prove2me | Theorems.Thm_Hirsch_cube_fibre_lift_exponential_barrier
-- name    : Hirsch.cube_fibre_lift_exponential_barrier
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-20T13:22:18.458517+00:00
-- url     : https://prove2.me/theorems/0ca69a92-2b6d-43ea-857c-0e684e8b7248
-- title:
--   Every compatible opposite-cube lift requires exponentially many completion edges
-- statement:
--   Let Z be a coefficient segment sum in R^d whose presented generator family contains the indicator vector of every nonempty subset of coordinates. Let Q be any set such that [0,1]^d+Q is contained in Z. For ANY q0,q1 in Q such that q0 and the all-ones vector plus q1 are actual extreme points of Z, EVERY finite feasible-point walk between these two endpoints through nondegenerate whole exposed segments satisfies 2^d <= L+1. Equivalently it uses at least 2^d-1 original Z edges. No objective, endpoint coefficient saturation, injective generator representation, graph, one-direction-per-edge oracle or path-length bound is supplied. Cube containment, the indicator-generator representation and actual endpoint extremality are explicit structural hypotheses; compatible endpoint existence is not asserted. Q need not be convex, closed or compact and containment need not be equality. The proof derives endpoint coefficients zero/one in every feasible representation from extremality and translated cube segments. Distinct nonempty Boolean directions then require different changing steps, using the accepted original-edge direction theorem. Unselected generators are unrestricted. The label map is defined on all subsets, so it requires a nonempty presented index type even in dimension zero; its empty-subset value is unused. This is a lower bound in the enlarged Z, not in the original cube, not an obstruction to every completion, and not a counterexample to Polynomial Hirsch. Only unweighted completion distance is constrained; contracted stationary steps may be discarded.
-- source:
--   Distinct endpoint-fibre continuation after accepted #317, Hirsch.zonotope_selected_direction_lower_bound, theorem75191fbb-65af-4558-b604-41faefe019f3, proofef6b66fdc467b8a01dee0d7c10d31cc9f35bd1f6. Reuses its actual namespace prefix through exists_change unchanged, excluding the old antipodal theorem and public root. New extremality-based endpoint saturation, Boolean-direction separation and exact powerset count strengthen the project application from existence of globally distant antipodes to EVERY compatible lift over two specified cube corners. The canonical all-pairs cube-completion application is explained separately, not an extra Lean equality/translation theorem. Classical Minkowski contraction is credited to Deza and Pournin, arXiv:1806.07643; no historical-priority claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.cube_fibre_lift_exponential_barrier (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (label : Finset (Fin d) → Fin m)
    (hlabel : ∀ S : Finset (Fin d), S.Nonempty → ∀ j,
      w (label S) j = if j ∈ S then 1 else 0)
    (Q : Set (Fin d → ℝ)) (q₀ q₁ : Fin d → ℝ) (hq₀ : q₀ ∈ Q) (hq₁ : q₁ ∈ Q) :
    let Z : Set (Fin d → ℝ) := {z | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=z}
    (∀ x : Fin d → ℝ, (∀ j, 0 ≤ x j ∧ x j ≤ 1) → ∀ q ∈ Q, x+q ∈ Z) →
    q₀ ∈ Z.extremePoints ℝ → (fun _ : Fin d => (1 : ℝ))+q₁ ∈ Z.extremePoints ℝ →
    ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin d → ℝ),
      p 0=q₀ → p (Fin.last L)=(fun _ => (1 : ℝ))+q₁ → (∀ i, p i ∈ Z) →
      (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
        IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ))) → 2^d ≤ L+1 := by sorry
