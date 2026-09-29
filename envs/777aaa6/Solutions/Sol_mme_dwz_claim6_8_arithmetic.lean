-- Prove2me | solution 1 for mme_dwz_claim6_8_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T09:06:18.482594+00:00
-- url     : https://prove2.me/submissions/0803f08c-cbbc-4a11-a678-cde93d8db732

import Mathlib.Tactic

theorem solution
    (Nalpha NBZ pcomp M : ℝ)
    (hNalpha : 0 ≤ Nalpha) (hpcomp : 0 ≤ pcomp)
    (hNBZ : 0 < NBZ) (hM : 0 < M)
    (hmodulus : 8 * Nalpha * pcomp / NBZ ≤ M) :
    Nalpha * pcomp / (NBZ * M) ≤ 1 / 8 := by
  have hNBZM : 0 < NBZ * M := mul_pos hNBZ hM
  have hnumerator : 0 ≤ Nalpha * pcomp := mul_nonneg hNalpha hpcomp
  have hscaled : 8 * (Nalpha * pcomp) ≤ NBZ * M := by
    apply (div_le_iff₀ hNBZ).mp at hmodulus
    nlinarith [hnumerator]
  apply (div_le_iff₀ hNBZM).2
  norm_num
  nlinarith [hnumerator]
