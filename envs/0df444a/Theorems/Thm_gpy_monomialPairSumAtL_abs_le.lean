-- Prove2me | Theorems.Thm_gpy_monomialPairSumAtL_abs_le
-- name    : gpy_monomialPairSumAtL_abs_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:18:02.732004+00:00
-- url     : https://prove2.me/theorems/93c00339-2130-4a6f-b4e9-1217cbe67ed7
-- title:
--   Per-modulus monomial piece bounded by the squared divisor count
-- statement:
--   Let $h = (h_1, \dots, h_k)$ be a tuple of shifts, let $R \geq 2$ be a level, let $a, b$ be monomial indices, let $i$ be a coordinate, and let $L$ be a modulus. Consider the tuples $d, e$ of positive integers with each entry at most $R$ and total product at most $R$. A pair $(d, e)$ is good at $i$ when some witness $w$ satisfies the joint divisibility system $\mathrm{lcm}(d_j, e_j) \mid w + h_j$ for all $j$ and $w + h_i$ is coprime to the combined modulus $L(d, e) = \mathrm{lcm}_j \mathrm{lcm}(d_j, e_j)$. The monomial piece at exact modulus $L$ is the sum over good pairs with $L(d, e) = L$ of $\mu(\prod d)\mu(\prod e) (-\log \prod d / \log R)^a (-\log \prod e / \log R)^b$. Then
--
--   $$\left| \text{piece at } L \right| \leq \tau_{k+1}(L)^2,$$
--
--   where $\tau_{k+1}(L)$ counts ordered factorizations of $L$ into $k+1$ positive factors. This is the error-side control for the monomial evaluation: every surviving term has Möbius factor at most $1$ in absolute value and log-ratio at most $1$, and the number of surviving good pairs at modulus $L$ is at most $\tau_{k+1}(L)^2$ by the Selberg fiber bound. Formalization Note: the support set, the good-pair condition, and the divisor count are all unfolded into explicit finite sums, filters, and cardinalities.
-- source:
--   GPY conditional monomial evaluation: the per-modulus monomial piece is bounded by the fiber count, from the tuple support, the Möbius bound, the log-ratio bound on the support, and the Selberg fiber bound

import Mathlib
open Classical

theorem gpy_monomialPairSumAtL_abs_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (L : ℕ) (hR : 2 ≤ R) :
    abs (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
        ∧ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
      then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
          * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
          * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
          * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
      else 0)
      ≤ (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card : ℝ) ^ 2 := by sorry
