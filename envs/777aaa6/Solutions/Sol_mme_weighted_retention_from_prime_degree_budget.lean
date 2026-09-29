-- Prove2me | solution 1 for mme_weighted_retention_from_prime_degree_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:29:50.26362+00:00
-- url     : https://prove2.me/submissions/f2630c78-d07e-416e-8440-7f780a089b74

import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (P D F S C M B V : ℝ)
    (hP : 0 < P) (hD : 0 < D) (hF : 0 < F)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hprime : P ≤ D * F)
    (hlabels : 6 * D ≤ S)
    (hkept : C * (S / (2 * P ^ 2)) ≤ M)
    (hbudget : V * D * F ^ 2 < C * B) :
    V < M * B := by
  have hp2 : 0 < 2 * P ^ 2 := by positivity
  have hcount : C * S ≤ M * (2 * P ^ 2) := by
    apply (div_le_iff₀ hp2).mp
    simpa only [mul_div_assoc] using hkept
  have hleft : 6 * D * C ≤ M * (2 * P ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlabels hC
    nlinarith
  have hsq : P ^ 2 ≤ (D * F) ^ 2 :=
    pow_le_pow_left₀ hP.le hprime 2
  have hright : M * (2 * P ^ 2) ≤ M * (2 * (D * F) ^ 2) := by
    gcongr
  have hboth := hleft.trans hright
  have hmargin : C ≤ M * (D * F ^ 2) := by
    nlinarith [mul_pos hD hF]
  have hweighted := mul_le_mul_of_nonneg_right hmargin hB
  have hpos : 0 < D * F ^ 2 := by positivity
  apply (mul_lt_mul_iff_left₀ hpos).mp
  nlinarith
