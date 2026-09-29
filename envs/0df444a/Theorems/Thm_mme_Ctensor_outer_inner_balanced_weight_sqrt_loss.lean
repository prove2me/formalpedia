-- Prove2me | Theorems.Thm_mme_Ctensor_outer_inner_balanced_weight_sqrt_loss
-- name    : mme_Ctensor_outer_inner_balanced_weight_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:58:01.826219+00:00
-- url     : https://prove2.me/theorems/a1e97d44-20e7-44fd-b084-5e78866d9c5f
-- title:
--   Two multinomial balances fit one square-root loss envelope
-- statement:
--   Fix positive integers $A,H,v$ and a real $\tau$ with $3\tau\ge2$. Put $n=A^3$, $r=Hm$, and $R=nr$. Let $W_{\mathrm{out}}$ count balanced length-$R$ words on $n$ letters with multiplicity $r$, and let $W_{\mathrm{in}}$ count balanced length-$r$ words on $H$ letters with multiplicity $m$. There is a constant $C\ge0$, independent of $m$, such that eventually
--
--   $$
--   \left(A^3H^2(v^3)^\tau\right)^R e^{-C\sqrt{R+1}}\le W_{\mathrm{out}}\left(W_{\mathrm{in}}^2e^{-100\sqrt{\log(W_{\mathrm{in}}+1)}}\right)^n\left(v^{3R}\right)^\tau.
--   $$
--
--   Thus the outer balance over $A^3$ ordered triples, all $A^3$ inner balances, and the induced-matching loss can be charged to one subexponential square-root envelope. This theorem is purely analytic and counting-theoretic; it makes no tensor restriction claim.
-- source:
--   The balanced-word multinomial estimates underlying V. Strassen's C-tensor value method, as used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271–272; https://doi.org/10.1016/S0747-7171(08)80013-2. Formal quantitative inputs are the Prove2Me theorems mme_Ctensor_balanced_word_card_coarse_lower and mme_Ctensor_balanced_count_matching_sqrt_loss.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

theorem mme_Ctensor_outer_inner_balanced_weight_sqrt_loss
    (A H volume : ℕ) (hA : 0 < A) (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let n : ℕ := A ^ 3
        let r : ℕ := H * m
        let R : ℕ := n * r
        let Wouter : ℕ :=
          Nat.card
            {w : Fin R → Fin n // ∀ p,
              Fintype.card {j // w j = p} = r}
        let Winner : ℕ :=
          Nat.card
            {w : Fin r → Fin H // ∀ h,
              Fintype.card {j // w j = h} = m}
        ((((A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
              (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
            Real.exp
              (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
          ((Wouter : ℝ) *
            (((Winner : ℝ) ^ 2 *
                Real.exp
                  (-100 * Real.sqrt
                    (Real.log (((Winner + 1 : ℕ) : ℝ))))) ^ n)) *
            (((volume ^ (3 * R) : ℕ) : ℝ) ^ tau)) := by
  sorry
