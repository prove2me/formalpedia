-- Prove2me | solution 1 for TropicalConeHull.colorful_caratheodory
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:35:29.364921+00:00
-- url     : https://prove2.me/submissions/2d287ceb-2821-497d-8353-c23a5889d6e8

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
theorem solution(hd : 0 < d) (p : Fin d → ι → Fin d → ℝ)
    (F : Fin d → Finset ι) (z : Fin d → ℝ)
    (hz : ∀ c, z ∈ tropConeHull (p c) (F c)) :
    ∃ (sel : Fin d → ι) (w : Fin d → ℝ), (∀ c, sel c ∈ F c) ∧
      ∀ i, z i = (univ : Finset (Fin d)).sup'
        ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun c => w c + p c (sel c) i) := by
  classical
  choose lam hFne hzeq using hz
  have hchoice : ∀ c : Fin d, ∃ k ∈ F c,
      (F c).sup' (hFne c) (fun k => lam c k + p c k c) = lam c k + p c k c :=
    fun c => Finset.exists_mem_eq_sup' (hFne c) _
  choose sel hselF hsel using hchoice
  refine ⟨sel, fun c => lam c (sel c), hselF, fun i => ?_⟩
  refine le_antisymm ?_ (Finset.sup'_le _ _ (fun c _ => ?_))
  · -- coordinate `i` is covered by the generator chosen for colour `i`
    have h1 : z i = lam i (sel i) + p i (sel i) i := by rw [hzeq i i, hsel i]
    rw [h1]
    exact Finset.le_sup' (fun c => lam c (sel c) + p c (sel c) i) (Finset.mem_univ i)
  · -- every chosen generator is dominated by `z`
    rw [hzeq c i]
    exact Finset.le_sup' (fun k => lam c k + p c k i) (hselF c)
