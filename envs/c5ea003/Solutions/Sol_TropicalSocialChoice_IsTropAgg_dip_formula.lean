-- Prove2me | solution 1 for TropicalSocialChoice.IsTropAgg.dip_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T19:09:57.947922+00:00
-- url     : https://prove2.me/submissions/7081cb9c-101a-4eb3-aeb0-a1a74aee6b81

import Mathlib
import Definitions.Def_Tropical_SocialChoice_TropicalArrow
open TropicalSocialChoice TropicalSocialChoice.IsTropAgg Finset in
theorem solution {ι : Type*} [DecidableEq ι] {F : (ι → ℝ) → ℝ} (h : IsTropAgg F) {i : ι}
    {t₀ : ℝ} (ht₀ : t₀ ≤ 0)
    (hc : F (dip i t₀) < 0) {u : ℝ} (hu : u ≤ 0) :
    F (dip i u) = min (u + (F (dip i t₀) - t₀)) 0 := by
  -- the upper dip formula: for `s ≤ v ≤ 0`, `F (dip i v) = min (v + (F (dip i s) - s)) 0`
  have hup : ∀ s v : ℝ, s ≤ v → v ≤ 0 → F (dip i v) = min (v + (F (dip i s) - s)) 0 := by
    intro s v hsv hv
    have e1 : F (dip i v) = min (F (fun k => dip i s k + (v - s))) (F (fun _ => 0)) := by
      rw [← h.min_hom]
      congr 1
      funext j
      simp only [dip]
      split_ifs with hj
      · rw [min_eq_left (by linarith)]
        ring
      · rw [min_eq_right (by linarith)]
    rw [e1, h.trans_eq, h.norm]
    congr 1
    ring
  rcases le_total t₀ u with htu | hut
  · exact hup t₀ u htu hu
  · -- run the formula backwards from `u` to `t₀`, then use `F (dip i t₀) < 0`
    have h1 := hup u t₀ hut ht₀
    have h2 := hup u u le_rfl hu
    have hlt : t₀ + (F (dip i u) - u) < 0 := by
      by_contra hge
      rw [min_eq_right (le_of_not_gt hge)] at h1
      linarith
    rw [min_eq_left hlt.le] at h1
    have hnp : F (dip i u) ≤ 0 := by
      rw [h2]
      exact min_le_right _ _
    rw [min_eq_left (by linarith)]
    linarith
