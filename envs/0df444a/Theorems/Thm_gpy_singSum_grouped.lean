-- Prove2me | Theorems.Thm_gpy_singSum_grouped
-- name    : gpy_singSum_grouped
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T17:10:04.690924+00:00
-- url     : https://prove2.me/theorems/ce0fc47c-ec58-47a7-a24c-f5540f3bfb9f
-- title:
--   Selberg singular sum in grouped form over moduli
-- statement:
--   Let h be a tuple of shifts, R a level, deg a degree, and i a coordinate. Let the Selberg weight be lam_d = mu(prod d) * (1 - log(prod d)/log R)^deg when prod d <= R, and 0 otherwise, and let the singular sum be the sum over good support pairs (d, e) of lam_d * lam_e / phi(L), where L is the combined modulus (the lcm of the coordinatewise lcms) and a pair is good at i when some witness w of the joint divisibility system has w + h_i coprime to L. Then the singular sum equals the sum over monomial indices a, b <= deg of (deg choose a)(deg choose b) times the sum over moduli L in [1, R^2] of (1/phi(L)) times the monomial pair sum at exact modulus L (the mu-weighted log-power sum over good pairs with combined modulus exactly L). This is the grouped form of the Selberg singular sum; the full singular-series evaluation to S(h) times an integral remains open and is not claimed here.
-- source:
--   GPY monomial-sum evaluation: the Selberg singular sum in fully grouped form, from the tuple support, the Selberg weight, the monomial expansion of the singular sum, and the monomial sums grouped by combined modulus

import Mathlib
open Classical

theorem gpy_singSum_grouped {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          * (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
      else 0)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ L ∈ Finset.Icc 1 (R ^ 2),
            (1 / ((Nat.totient L : ℕ) : ℝ)) *
              (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
                  ∧ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                    Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
                then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                    * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                    * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                    * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
                else 0) := by sorry
