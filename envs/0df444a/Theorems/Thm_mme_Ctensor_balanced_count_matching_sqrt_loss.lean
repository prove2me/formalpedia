-- Prove2me | Theorems.Thm_mme_Ctensor_balanced_count_matching_sqrt_loss
-- name    : mme_Ctensor_balanced_count_matching_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:37:22.52534+00:00
-- url     : https://prove2.me/theorems/81932fb6-2894-4054-a9fe-12ad3a2c02df
-- title:
--   Balanced type counts absorb the induced-matching loss
-- statement:
--   Fix a positive integer $H$. For $R=Hm$, let $W$ be the number of balanced length-$R$ words on $H$ letters. Then there is a constant $C\ge0$ such that, for all sufficiently large $m$,
--
--   $$
--   H^{2R}e^{-C\sqrt{R+1}}\le W^2e^{-100\sqrt{\log(W+1)}}.
--   $$
--
--   The balanced multinomial class has size $H^{R-o(R)}$, and its fixed-degree polynomial loss is small enough that even after a Behrend induced-matching loss, the full base $H^{2R}$ remains up to one square-root exponential envelope.
-- source:
--   Balanced multinomial estimate combined with the Behrend induced-matching bound in Strassen's C-tensor method; see D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 271--272.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finite.Card
import Theorems.Thm_mme_Ctensor_balanced_word_card_coarse_lower

open BigOperators Filter

set_option autoImplicit false

theorem mme_Ctensor_balanced_count_matching_sqrt_loss
    (H : ℕ) (hH : 0 < H) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let R : ℕ := H * m
        let W : ℕ :=
          Nat.card
            {w : Fin R → Fin H // ∀ h,
              Fintype.card {j // w j = h} = m}
        ((H : ℝ) ^ (2 * R)) *
            Real.exp
              (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
          (W : ℝ) ^ 2 *
            Real.exp
              (-100 * Real.sqrt
                (Real.log (((W + 1 : ℕ) : ℝ)))) := by
  sorry
