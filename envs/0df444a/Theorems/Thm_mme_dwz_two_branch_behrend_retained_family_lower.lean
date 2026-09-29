-- Prove2me | Theorems.Thm_mme_dwz_two_branch_behrend_retained_family_lower
-- name    : mme_dwz_two_branch_behrend_retained_family_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T14:47:09.807015+00:00
-- url     : https://prove2.me/theorems/15756211-f47a-4b72-a680-795f44b71c9c
-- title:
--   Explicit two-branch prime and Behrend retained-family normalization
-- statement:
--   Suppose a global exact-type count factors as A = ZT, the two source branches have entropy numerators exp(xA) and exp(xZ) with explicit polynomial losses, the first collision degree and compatibility budget have exponents exp(xd) and exp(xp), and one fixed-target Behrend hash retains I objects. If the common prime is bounded by 16 max(d,R), then the restored Z-fold count is bounded below by the minimum branch exponential times the explicit floor(p/2)/p, Behrend exponential, and polynomial factors displayed in the Lean statement. No polynomial, prime-floor, or Salem--Spencer loss is absorbed into asymptotic notation.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, asymmetric-hashing retained count in Equation (21), Section 6.2, printed pp. 53-54, combined with the explicit lower-half Behrend loss used in Section 3.10; https://arxiv.org/abs/2210.10173

import Mathlib
set_option autoImplicit false

theorem mme_dwz_two_branch_behrend_retained_family_lower
    (A Z T d p I : ℕ) (R Pa Pd Pz Pr xA xZ xd xp : ℝ)
    (hfactor : A = Z * T)
    (hdpos : 0 < d) (hppos : 0 < p)
    (hPa : 0 < Pa) (hPd : 0 < Pd) (hPz : 0 < Pz) (hPr : 0 < Pr)
    (hA : Real.exp xA ≤ Pa * (A : ℝ))
    (hZ : Real.exp xZ ≤ Pz * (Z : ℝ))
    (hd : (d : ℝ) ≤ Pd * Real.exp xd)
    (hR : R = Pr * (T : ℝ) * Real.exp xp)
    (hp : (p : ℝ) ≤ 16 * max (d : ℝ) R)
    (hretained :
      ((T : ℝ) *
          (((p / 2 : ℕ) : ℝ) *
            Real.exp (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ)))))) /
          (2 * (p : ℝ) ^ 2) ≤ (I : ℝ)) :
    Real.exp (min (xA - xd) (xZ - xp)) *
          (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
            Real.exp (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ)))))) /
          (32 * max (Pa * Pd) (Pz * Pr)) ≤
      (Z : ℝ) * (I : ℝ) := by
  sorry
