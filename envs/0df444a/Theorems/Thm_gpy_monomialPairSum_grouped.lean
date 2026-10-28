-- Prove2me | Theorems.Thm_gpy_monomialPairSum_grouped
-- name    : gpy_monomialPairSum_grouped
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T17:10:08.961176+00:00
-- url     : https://prove2.me/theorems/9a29ad0d-84b0-4dd1-9992-ae432857ed46
-- title:
--   Monomial pair sum grouped by exact modulus
-- statement:
--   Let h be a tuple of shifts, R a level, a and b monomial indices, and i a coordinate. The monomial pair sum (the mu-weighted log-power sum over good support pairs, divided by phi of the combined modulus L) equals the sum over moduli L in [1, R^2] of (1/phi(L)) times the monomial pair sum at exact modulus L (the same sum restricted to good pairs whose combined modulus is exactly L). The level bound L <= R^2 for support pairs keeps the modulus range finite.
-- source:
--   GPY monomial-sum evaluation: the monomial pair sum grouped by combined modulus, from the tuple support and the level bound L <= R^2 for support pairs

import Mathlib
open Classical

theorem gpy_monomialPairSum_grouped {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
          * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
          * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
          * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
      else 0)
      = ∑ L ∈ Finset.Icc 1 (R ^ 2),
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
