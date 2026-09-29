-- Prove2me | solution 1 for Moebius.ZM.zeroDivisor_iff_nrm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T14:56:30.701748+00:00
-- url     : https://prove2.me/submissions/b4a8f99e-d96c-4161-ba23-9319845f7fc7

import Definitions.Def_MachineLearning_MoebiusTwistRing
open Moebius Moebius.ZM in
theorem solution (z : ZM) :
    (∃ w : ZM, w ≠ 0 ∧ z * w = 0) ↔ nrm z = 0 := by
  obtain ⟨⟨u, v⟩, hz⟩ := z
  simp only [nrm]
  constructor
  · rintro ⟨⟨⟨p, q⟩, hw⟩, hw0, hzw⟩
    have h := congrArg Subtype.val hzw
    simp only [MulMemClass.coe_mul, ZeroMemClass.coe_zero, Prod.mk_mul_mk, Prod.mk_eq_zero] at h
    by_contra huv
    have hu : u ≠ 0 := fun h0 => huv (by simp [h0])
    have hv : v ≠ 0 := fun h0 => huv (by simp [h0])
    have hp : p = 0 := (mul_eq_zero.mp h.1).resolve_left hu
    have hq : q = 0 := (mul_eq_zero.mp h.2).resolve_left hv
    apply hw0
    subst hp hq
    rfl
  · intro huv
    rcases mul_eq_zero.mp huv with hu | hv
    · refine ⟨⟨(2, 0), ⟨1, by norm_num⟩⟩, ?_, ?_⟩
      · intro h
        have := congrArg (fun w : ZM => (w : ℤ × ℤ).1) h
        simp at this
      · apply Subtype.ext
        simp [hu]
    · refine ⟨⟨(0, 2), ⟨-1, by norm_num⟩⟩, ?_, ?_⟩
      · intro h
        have := congrArg (fun w : ZM => (w : ℤ × ℤ).2) h
        simp at this
      · apply Subtype.ext
        simp [hv]
