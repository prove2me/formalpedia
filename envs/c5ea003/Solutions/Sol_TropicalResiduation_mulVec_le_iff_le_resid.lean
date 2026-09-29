-- Prove2me | solution 1 for TropicalResiduation.mulVec_le_iff_le_resid
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:56:39.190296+00:00
-- url     : https://prove2.me/submissions/c4d362c5-b7e4-485a-a6cd-fa01a62d4407

-- Sol generated from Tropical/TropicalConvexity/ConeHullOptimization.lean
import Mathlib
import Definitions.Def_Tropical_TropicalConvexity_ConeHullOptimization

/-!
# Tropical cone hulls, Carathéodory number `d`, and max-plus residuation

This file complements the tropical Helly theory with the two other pillars of
tropical convexity: the **Carathéodory number** of tropical cones in `ℝ^d`
(which is `d`, one better than the affine normalized bound `d + 1`), and the
**optimization side**: the residuation (Galois) correspondence for max-plus
linear systems, giving the greatest subsolution of `A ⊗ x ≤ b` together with a
complete solvability criterion for `A ⊗ x = b`.

## Main results

* `TropicalConeHull.tropical_caratheodory_cone` — Carathéodory number `d`.
* `TropicalConeHull.caratheodory_cone_sharp` — the bound `d` cannot be improved.
* `TropicalConeHull.colorful_caratheodory` — colourful Carathéodory theorem.
* `TropicalConeHull.dependence_of_helly` — the converse implication
  "tropical Helly ⇒ tropical Cramer dependence", so that the Helly theorem of
  `HellyNumber.lean` and the dependence theorem behind it are *equivalent*.
* `TropicalResiduation.mulVec_le_iff_le_resid` — the residuation Galois
  connection for max-plus linear inequalities.
* `TropicalResiduation.tropical_solvable_iff` — `A ⊗ x = b` is solvable iff the
  canonical candidate `resid A b` solves it (Cuninghame-Green's principal
  solution): an `O(mn)` decision procedure for max-plus linear systems.
-/

open Finset

open TropicalConeHull

variable {d : ℕ} {ι : Type*}






/-! ## The tropical Helly property is *equivalent* to tropical dependence

`HellyNumber.lean` proves the implication "Cramer dependence ⇒ tropical Helly".
Here we close the loop: the Helly property, taken as a hypothesis, forces
`d + 1` points of `ℝ^d` to be tropically dependent.  So the two statements are
two faces of the same phenomenon. -/







open TropicalResiduation

variable {m n : ℕ}









open TropicalResiduation in
theorem solution(A : Fin (m + 1) → Fin (n + 1) → ℝ)
    (b : Fin (m + 1) → ℝ) (x : Fin (n + 1) → ℝ) :
    (∀ i, mulVec A x i ≤ b i) ↔ (∀ j, x j ≤ resid A b j) := by
  constructor
  · intro h j
    refine Finset.le_inf' _ _ (fun i _ => ?_)
    have h1 : A i j + x j ≤ mulVec A x i :=
      Finset.le_sup' (fun j => A i j + x j) (Finset.mem_univ j)
    have := h i
    linarith
  · intro h i
    refine Finset.sup'_le _ _ (fun j _ => ?_)
    have h1 : resid A b j ≤ b i - A i j :=
      Finset.inf'_le (fun i => b i - A i j) (Finset.mem_univ i)
    have := h j
    linarith
