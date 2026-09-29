-- Prove2me | solution 1 for TropicalSocialChoice.IsTropAgg.dip_formula_upper
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T19:05:24.384009+00:00
-- url     : https://prove2.me/submissions/15202b39-85d2-4596-8b34-6d895ced28be

import Mathlib
import Definitions.Def_Tropical_SocialChoice_TropicalArrow
open TropicalSocialChoice TropicalSocialChoice.IsTropAgg Finset in
theorem solution {ι : Type*} [DecidableEq ι] {F : (ι → ℝ) → ℝ} (h : IsTropAgg F) {i : ι}
    {t₀ : ℝ} {u : ℝ} (hu₀ : t₀ ≤ u) (hu : u ≤ 0) :
    F (dip i u) = min (u + (F (dip i t₀) - t₀)) 0 := by
  -- `dip i u` is the tropical sum of the shifted dip at `t₀` and the zero profile
  have e1 : F (dip i u) = min (F (fun k => dip i t₀ k + (u - t₀))) (F (fun _ => 0)) := by
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
