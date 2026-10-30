-- Prove2me | Theorems.Thm_gpy_monomialPairSum_abs_le
-- name    : gpy_monomialPairSum_abs_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:21:33.752363+00:00
-- url     : https://prove2.me/theorems/2fa8e397-19d8-4bf8-bbea-4dd39c4b63a9
-- title:
--   Monomial pair sum bounded by the finite tau-squared sum over moduli
-- statement:
--   Let $h$ be a tuple of shifts, let $R \geq 2$ be a level, let $a, b$ be monomial indices, and let $i$ be a coordinate. The monomial pair sum is the sum over good support pairs $(d, e)$ of $\mu(\prod d)\mu(\prod e) (-\log \prod d / \log R)^a (-\log \prod e / \log R)^b / \varphi(L(d, e))$, where $L(d, e)$ is the combined modulus and goodness at $i$ is the witness condition described in the companion per-modulus bound. Then
--
--   $$\left| \text{monomial pair sum} \right| \leq \sum_{1 \leq L \leq R^2} \tau_{k+1}(L)^2,$$
--
--   using $1/\varphi(L) \leq 1$ for $L \geq 1$ and the per-modulus bound at each $L$. The modulus range is finite because every support pair has combined modulus at most $R^2$. This is the whole-sum form of the error-side control for the monomial evaluation. Formalization Note: the support set, the good-pair condition, and the divisor count are all unfolded into explicit finite sums, filters, and cardinalities.
-- source:
--   GPY conditional monomial evaluation: the whole monomial sum is bounded by the finite tau-squared sum, from the modulus grouping and the per-modulus bound

import Mathlib
open Classical

theorem gpy_monomialPairSum_abs_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (hR : 2 ≤ R) :
    abs (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
          * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
          * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
          * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
      else 0)
      ≤ ∑ L ∈ Finset.Icc 1 (R ^ 2),
        (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
          (fun d => ∏ i, d i = L)).card : ℝ) ^ 2 := by sorry
