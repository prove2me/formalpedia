-- Prove2me | Theorems.Thm_mme_phi233_profile_product_mono_of_entropy_cost_le
-- name    : mme_phi233_profile_product_mono_of_entropy_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:21:09.761145+00:00
-- url     : https://prove2.me/theorems/2381cfcd-cbad-4b43-8645-659d1bd8285c
-- title:
--   Entropy-cost comparison implies phi_233 profile-product comparison
-- statement:
--   Let $a,b,c,d,a',b',c',d'$ be nonnegative real numbers. If their continuous logarithmic profile costs satisfy $$2a\log a+b\log b+c\log c+d\log d\le 2a'\log a'+b'\log b'+c'\log c'+d'\log d',$$ using the convention $0\log 0=0$, then their profile products satisfy $$a^{2a}b^bc^cd^d\le (a')^{2a'}(b')^{b'}(c')^{c'}(d')^{d'}.$$ This bridge converts the compact entropy minimization for the nontrivial $\varphi_{233}$ marginal fiber into the multiplicative completion-factor inequality used in the type-2 estimate.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (3.6) on p. 360 and Lemma 5.1(v) on p. 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

theorem mme_phi233_profile_product_mono_of_entropy_cost_le
    (a b c d a' b' c' d' : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') (hd' : 0 ≤ d')
    (hcost :
      -2 * Real.negMulLog a - Real.negMulLog b -
          Real.negMulLog c - Real.negMulLog d ≤
        -2 * Real.negMulLog a' - Real.negMulLog b' -
          Real.negMulLog c' - Real.negMulLog d') :
    a ^ (2 * a) * b ^ b * c ^ c * d ^ d ≤
      a' ^ (2 * a') * b' ^ b' * c' ^ c' * d' ^ d' := by
  sorry
