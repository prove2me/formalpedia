-- Prove2me | solution 1 for MovingSofa.ForMathlib.hasDerivWithinAt_Icc_of_oneSided
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-03T20:52:29.843259+00:00
-- url     : https://prove2.me/submissions/977a717a-cb47-4ffa-9fbd-9880d944868b

import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open Set

theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) {f : ℝ → E} {d : E}
    (hr : t < b → HasDerivWithinAt f d (Ici t) t)
    (hl : a < t → HasDerivWithinAt f d (Iic t) t) :
    HasDerivWithinAt f d (Icc a b) t := by
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact (hr hab).mono Icc_subset_Ici_self
  · rcases lt_or_eq_of_le ht.2 with htb | rfl
    · have h := (hl hat).union (hr htb)
      rw [Iic_union_Ici] at h
      exact h.mono (subset_univ _)
    · exact (hl hat).mono Icc_subset_Iic_self
