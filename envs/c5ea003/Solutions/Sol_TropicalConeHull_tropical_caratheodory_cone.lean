-- Prove2me | solution 1 for TropicalConeHull.tropical_caratheodory_cone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:35:30.424251+00:00
-- url     : https://prove2.me/submissions/5f7067a6-e5ad-4d2a-993f-36d84ff15164

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
theorem solution(hd : 0 < d) (p : ι → Fin d → ℝ)
    (F : Finset ι) (z : Fin d → ℝ) (hz : z ∈ tropConeHull p F) :
    ∃ G ⊆ F, G.card ≤ d ∧ z ∈ tropConeHull p G := by
  classical
  obtain ⟨lam, hF, hzeq⟩ := hz
  have hchoice : ∀ i : Fin d, ∃ k ∈ F,
      F.sup' hF (fun k => lam k + p k i) = lam k + p k i :=
    fun i => Finset.exists_mem_eq_sup' hF _
  choose kk hkkF hkk using hchoice
  have hdne : (univ : Finset (Fin d)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]; exact hd
  refine ⟨univ.image kk, ?_, ?_, lam, (hdne.image kk), fun i => ?_⟩
  · intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    exact hkkF i
  · exact le_trans Finset.card_image_le (by simp)
  · refine le_antisymm ?_ ?_
    · rw [hzeq i, hkk i]
      exact Finset.le_sup' (fun k => lam k + p k i)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    · rw [hzeq i]
      refine Finset.sup'_le _ _ (fun k hk => ?_)
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.le_sup' (fun k => lam k + p k i) (hkkF j)
