-- Prove2me | Theorems.Thm_mme_CW_q6_floor_rate_absorption
-- name    : mme_CW_q6_floor_rate_absorption
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:33:24.34861+00:00
-- url     : https://prove2.me/theorems/84345416-f6c2-4225-87cc-9862909a2e12
-- title:
--   Fixed q=6 floor losses are absorbed by one square-root exponential constant
-- statement:
--   Let $M=4X^2+1$. Suppose $M\le5Z$, $|S|\ge80$, $A\ge\lfloor |S|Z/(16M)\rfloor$, $B\ge400M$, and $H=\lfloor B/(8M)\rfloor$. If\n\n$$e^{-C\sqrt{N+1}}\le\frac{|S|/M}{N+1},$$\n\nthen increasing the loss constant by $\log 32$ absorbs both natural-number floors at once:\n\n$$Z e^{-(C+\log32)\sqrt{N+1}}\le A,$$\n\n$$B e^{-(C+\log32)\sqrt{N+1}}\le4X^2H.$$\n\nThe hypotheses $|S|\ge80$ and $M\le5Z$ ensure the first quotient is nonzero; the margin $B\ge400M$ controls the second quotient. No endpoint limit or tensor assertion occurs here.
-- source:
--   Elementary floor and exponential-loss bookkeeping for the q=6 Coppersmith--Winograd affine hash.

import Mathlib
import Theorems.Thm_mme_nat_div_real_half_lower

open Filter Topology

set_option autoImplicit false

theorem mme_CW_q6_floor_rate_absorption
    {N S Z X B M A H : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hX : 0 < X)
    (hM : M = 4 * X ^ 2 + 1)
    (hMZ : M ≤ 5 * Z)
    (hS : 80 ≤ S)
    (hA : (S * Z) / (16 * M) ≤ A)
    (hlarge : 400 * M ≤ B)
    (hH : H = B / (8 * M))
    (hdensity :
      Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (S : ℝ) / (M : ℝ) / (((N + 1 : ℕ) : ℝ))) :
    (Z : ℝ) *
          Real.exp (-(C + Real.log 32) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (A : ℝ) ∧
      (B : ℝ) *
          Real.exp (-(C + Real.log 32) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        4 * (X : ℝ) ^ 2 * (H : ℝ) := by
  sorry
