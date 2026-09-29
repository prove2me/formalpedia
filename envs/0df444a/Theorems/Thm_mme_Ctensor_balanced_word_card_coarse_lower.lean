-- Prove2me | Theorems.Thm_mme_Ctensor_balanced_word_card_coarse_lower
-- name    : mme_Ctensor_balanced_word_card_coarse_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:30:21.166931+00:00
-- url     : https://prove2.me/theorems/9951eaf2-f3e1-4384-8996-40ffac2d1149
-- title:
--   A polynomial-loss lower bound for the balanced C-tensor type class
-- statement:
--   Let $H,m>0$, and let $W_{H,m}$ be the number of length-$Hm$ words over an $H$-letter alphabet in which every letter occurs exactly $m$ times. Then
--
--   $$
--   H^{Hm}\le \bigl(6(m+1)\bigr)^H W_{H,m}.
--   $$
--
--   Thus the balanced type class retains the full exponential rate $H^{Hm}$ with only a fixed-degree polynomial loss in $m$. This explicit bound is the multinomial input needed by the finite C-tensor extraction.
-- source:
--   Elementary Stirling estimate for the balanced multinomial coefficient; used in Strassen's C-tensor method and in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 271--272.

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Theorems.Thm_mme_Ctensor_balanced_word_card

open BigOperators

set_option autoImplicit false

theorem mme_Ctensor_balanced_word_card_coarse_lower
    (H m : ℕ) (hH : 0 < H) (hm : 0 < m) :
    (H : ℝ) ^ (H * m) ≤
      (6 * (((m + 1 : ℕ) : ℝ))) ^ H *
        (Nat.card
          {w : Fin (H * m) → Fin H // ∀ h,
            Fintype.card {j // w j = h} = m} : ℝ) := by
  sorry
