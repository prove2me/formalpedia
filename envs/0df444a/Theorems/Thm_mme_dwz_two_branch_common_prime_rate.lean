-- Prove2me | Theorems.Thm_mme_dwz_two_branch_common_prime_rate
-- name    : mme_dwz_two_branch_common_prime_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T18:36:04.833044+00:00
-- url     : https://prove2.me/theorems/8509c3f9-d48b-4ee3-899f-dee3f2f05bb0
-- title:
--   Two-branch entropy normalization for a common asymmetric-hash prime
-- statement:
--   Let the global source count factor exactly as $A=ZT$. Suppose its two entropy numerators have lower bounds $e^{x_A}\le P_AA$ and $e^{x_Z}\le P_ZZ$, while the first collision degree and second compatibility budget satisfy $d\le P_de^{x_d}$ and $R=P_rTe^{x_p}$. If a common prime obeys $p\le16\max\{d,R\}$, then
--
--   $$p e^{\min\{x_A-x_d, x_Z-x_p\}}\le16\max\{P_AP_d,P_ZP_r\} A.$$
--
--   This is the exact two-branch finite normalization underlying the maximum denominator and minimum entropy exponent in DWZ Equation (21).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (21) and Section 6.2; https://arxiv.org/abs/2210.10173

import Mathlib

set_option autoImplicit false

theorem mme_dwz_two_branch_common_prime_rate
    (A Z T d p : ℕ) (R Pa Pd Pz Pr xA xZ xd xp : ℝ)
    (hfactor : A = Z * T)
    (hdpos : 0 < d)
    (_hPa : 0 < Pa) (hPd : 0 < Pd) (_hPz : 0 < Pz) (hPr : 0 < Pr)
    (hA : Real.exp xA ≤ Pa * (A : ℝ))
    (hZ : Real.exp xZ ≤ Pz * (Z : ℝ))
    (hd : (d : ℝ) ≤ Pd * Real.exp xd)
    (hR : R = Pr * (T : ℝ) * Real.exp xp)
    (hp : (p : ℝ) ≤ 16 * max (d : ℝ) R) :
    (p : ℝ) * Real.exp (min (xA - xd) (xZ - xp)) ≤
      16 * max (Pa * Pd) (Pz * Pr) * (A : ℝ) := by
  sorry
