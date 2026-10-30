-- Prove2me | Theorems.Thm_gpy_monomialPairSumAtL_eq_goodCount_sum
-- name    : gpy_monomialPairSumAtL_eq_goodCount_sum
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:27:50.343353+00:00
-- url     : https://prove2.me/theorems/48176532-09f4-4619-a618-dd55a7f088bf
-- title:
--   Per-modulus monomial piece regrouped by products via the good count
-- statement:
--   Let $h$ be a tuple of shifts, let $R$ be a level, let $a, b$ be monomial indices, let $i$ be a coordinate, and let $L$ be a modulus. The monomial piece at exact modulus $L$ is the sum over good support pairs $(d, e)$ with combined modulus $L$ of $\mu(\prod d)\mu(\prod e) (-\log \prod d / \log R)^a (-\log \prod e / \log R)^b$. Grouping the pairs by their products $D = \prod d$ and $E = \prod e$, the piece equals
--
--   $$\sum_{1 \leq D, E \leq R} \mu(D)\mu(E) (-\log D / \log R)^a (-\log E / \log R)^b \cdot N(h, R, i, D, E, L),$$
--
--   where $N(h, R, i, D, E, L)$ is the number of support pairs $(d, e)$ with $\prod d = D$, $\prod e = E$, good at $i$, and combined modulus $L$. The Möbius and log-power factor depends only on $(D, E)$, so it factors out of the fiber sum, leaving exactly this good count. This regrouping stages the remaining combinatorial problem: everything about the pair sum except the good count is now one-variable. Formalization Note: the support set, the good-pair condition, and the good count are all unfolded into explicit finite sums, filters, and cardinalities.
-- source:
--   GPY conditional monomial evaluation: regrouping of the per-modulus monomial piece by products, isolating the good count

import Mathlib
open Classical

theorem gpy_monomialPairSumAtL_eq_goodCount_sum {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (L : ℕ) :
    (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
        ∧ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
      then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
          * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
          * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
          * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
      else 0)
      = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b
          * ((((Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)
              ×ˢ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter
            (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧
              (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
                Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
              Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L)).card : ℝ) := by sorry
