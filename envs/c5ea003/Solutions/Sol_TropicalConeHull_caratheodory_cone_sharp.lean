-- Prove2me | solution 1 for TropicalConeHull.caratheodory_cone_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:35:28.800025+00:00
-- url     : https://prove2.me/submissions/a704aa29-ec0a-41ea-9f68-fc09c9f0c7b7

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
theorem solution(hd : 0 < d) :
    ∃ (p : Fin d → Fin d → ℝ) (z : Fin d → ℝ),
      z ∈ tropConeHull p univ ∧
      ∀ G : Finset (Fin d), G.card < d → z ∉ tropConeHull p G := by
  classical
  refine ⟨fun k i => if i = k then 0 else -1, fun _ => 0, ⟨fun _ => 0, ?_, fun i => ?_⟩, ?_⟩
  · exact ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  · refine le_antisymm ?_ ?_
    · have : (0 : ℝ) + (if i = i then (0:ℝ) else -1) ≤
          univ.sup' ⟨⟨0, hd⟩, Finset.mem_univ _⟩
            (fun k => (0:ℝ) + if i = k then (0:ℝ) else -1) :=
        Finset.le_sup' (fun k => (0:ℝ) + if i = k then (0:ℝ) else -1) (Finset.mem_univ i)
      simpa using this
    · refine Finset.sup'_le _ _ (fun k _ => ?_)
      by_cases h : i = k <;> simp [h]
  · rintro G hG ⟨lam, hGne, hz⟩
    -- some coordinate `i₀` is missing from `G`
    have hex : ∃ i₀ : Fin d, i₀ ∉ G := by
      by_contra hcon
      push_neg at hcon
      rw [Finset.eq_univ_of_forall hcon, Finset.card_univ, Fintype.card_fin] at hG
      exact lt_irrefl d hG
    obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨kstar, hkstar, hks⟩ := Finset.exists_mem_eq_sup' hGne
      (fun k => lam k + if i₀ = k then (0:ℝ) else -1)
    have hne : i₀ ≠ kstar := fun hcon => hi₀ (hcon ▸ hkstar)
    have h1 : lam kstar = 1 := by
      have := hz i₀
      rw [hks] at this
      simp only [hne, if_false] at this
      linarith
    have h2 : lam kstar + (if kstar = kstar then (0:ℝ) else -1)
        ≤ G.sup' hGne (fun k => lam k + if kstar = k then (0:ℝ) else -1) :=
      Finset.le_sup' (fun k => lam k + if kstar = k then (0:ℝ) else -1) hkstar
    have h3 : (if kstar = kstar then (0:ℝ) else -1) = 0 := by simp
    have h4 : G.sup' hGne (fun k => lam k + if kstar = k then (0:ℝ) else -1) = 0 :=
      (hz kstar).symm
    rw [h1, h3, add_zero, h4] at h2
    linarith
