-- Prove2me | solution 1 for TropicalConeHull.mem_tropConeHull_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:35:29.909682+00:00
-- url     : https://prove2.me/submissions/83bfdd1c-e431-4983-83e3-1a124d489b84

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









open TropicalConeHull in
theorem solution(hd : 0 < d) (p : ι → Fin d → ℝ) {F : Finset ι}
    {k₀ : ι} (hk₀ : k₀ ∈ F) : p k₀ ∈ tropConeHull p F := by
  classical
  have hdne : (univ : Finset (Fin d)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]; exact hd
  refine ⟨fun j => if j = k₀ then 0 else
      (univ.inf' hdne (fun i => p k₀ i)) - (univ.sup' hdne (fun i => p j i)),
    ⟨k₀, hk₀⟩, fun i => ?_⟩
  refine le_antisymm ?_ (Finset.sup'_le _ _ (fun j _ => ?_))
  · have := Finset.le_sup'
      (fun j => (if j = k₀ then (0:ℝ) else
        (univ.inf' hdne (fun i => p k₀ i)) - (univ.sup' hdne (fun i => p j i))) + p j i) hk₀
    simpa using this
  · by_cases hj : j = k₀
    · simp [hj]
    · simp only [hj, if_false]
      have h1 : univ.inf' hdne (fun i => p k₀ i) ≤ p k₀ i :=
        Finset.inf'_le (fun i => p k₀ i) (Finset.mem_univ i)
      have h2 : p j i ≤ univ.sup' hdne (fun i => p j i) :=
        Finset.le_sup' (fun i => p j i) (Finset.mem_univ i)
      linarith
