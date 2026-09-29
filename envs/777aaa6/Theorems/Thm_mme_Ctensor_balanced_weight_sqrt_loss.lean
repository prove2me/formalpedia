-- Prove2me | Theorems.Thm_mme_Ctensor_balanced_weight_sqrt_loss
-- name    : mme_Ctensor_balanced_weight_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:22:29.154033+00:00
-- url     : https://prove2.me/theorems/ae25d5a3-e4c5-4622-91aa-d165ab8a3f25
-- title:
--   Balanced C-tensor type weights retain the full base up to square-root loss
-- statement:
--   Fix positive integers $H,v$ and $\tau$ with $3\tau\ge2$. For $R=Hm$, let $W$ be the balanced multinomial coefficient counting length-$R$ words in which every one of the $H$ labels occurs $m$ times. Then there is a constant $C\ge0$ such that, for all sufficiently large $m$,
--
--   $$
--   \bigl(H^2(v^3)^\tau\bigr)^R e^{-C\sqrt{R+1}}
--   \le W^2e^{-100\sqrt{\log(W+1)}}\,(v^{3R})^\tau.
--   $$
--
--   This is the purely quantitative half of the C-tensor value argument. Stirling's estimate gives $W=H^{R-o(R)}$; the displayed square-root envelope simultaneously absorbs its polynomial multinomial loss and the Behrend induced-matching loss. The identity $(v^{3R})^\tau=((v^3)^\tau)^R$ accounts for the common volume of the three cyclic orientations.
-- source:
--   Multinomial/Stirling estimate in Strassen's C-tensor method, used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Stirling
import Theorems.Thm_mme_Ctensor_balanced_word_card

open BigOperators Filter

set_option autoImplicit false

theorem mme_Ctensor_balanced_weight_sqrt_loss
    (H volume : ℕ) (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let R : ℕ := H * m
        let W : ℕ :=
          Nat.card
            {w : Fin R → Fin H // ∀ h,
              Fintype.card {j // w j = h} = m}
        (((H : ℝ) ^ 2 *
              (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
            Real.exp
              (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
          ((W : ℝ) ^ 2 *
              Real.exp
                (-100 * Real.sqrt
                  (Real.log (((W + 1 : ℕ) : ℝ))))) *
            (((volume ^ (3 * R) : ℕ) : ℝ) ^ tau) := by
  sorry
