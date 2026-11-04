-- Prove2me | solution 1 for MovingSofa.ForMathlib.hasDerivAt_if_le
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:56:10.731441+00:00
-- url     : https://prove2.me/submissions/db83189a-a45b-4dcd-8434-5ddb3ee19a20

import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open Set

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g f' g' : ℝ → E} {c : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hfg : f c = g c) (hfg' : f' c = g' c) (t : ℝ) :
    HasDerivAt (fun s => if s ≤ c then f s else g s) (if t ≤ c then f' t else g' t) t := by
  rcases lt_trichotomy t c with ht | ht | ht
  · rw [if_pos ht.le]
    refine (hf t).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact if_pos (le_of_lt hs)
  · subst ht
    rw [if_pos le_rfl]
    have hl : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) (f' t) (Iic t) t :=
      (hf t).hasDerivWithinAt.congr (fun _ hs => if_pos hs) (if_pos le_rfl)
    have hr : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) (f' t) (Ici t) t := by
      rw [hfg']
      refine (hg t).hasDerivWithinAt.congr (fun s hs => ?_) (by rw [if_pos le_rfl, hfg])
      rcases eq_or_lt_of_le (mem_Ici.mp hs) with rfl | hlt
      · rw [if_pos le_rfl, hfg]
      · rw [if_neg (not_le.mpr hlt)]
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    exact hasDerivWithinAt_univ.mp hu
  · rw [if_neg (not_le.mpr ht)]
    refine (hg t).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact if_neg (not_le.mpr hs)
