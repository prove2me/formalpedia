-- Prove2me | Theorems.Thm_gpy_fiberWeight_sum_le_divWeightedErrSum
-- name    : gpy_fiberWeight_sum_le_divWeightedErrSum
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:20:08.308549+00:00
-- url     : https://prove2.me/theorems/9b47e3bf-835d-40bc-88d1-7fd91df92a9e
-- title:
--   Fiber-weighted error sums are bounded by divisor-weighted endpoint sums
-- statement:
--   Let $h = (h_1, \dots, h_k)$ be a tuple of shifts, let $R \geq 2$ be a level, let $\deg$ be a degree, let $i$ be a coordinate, and let $M$ be a model for prime counts in arithmetic progressions. For a modulus $L$, let the fiber weight at $i$ be the total $|\lambda_d \lambda_e|$ over support pairs $(d, e)$ whose combined modulus is $L$ and which are good at $i$, where $\lambda$ is the Selberg weight and goodness at $i$ is the witness condition (some $w$ satisfies the joint divisibility system and $w + h_i$ is coprime to the combined modulus). Let the max coprime-residue error at height $Y$ and modulus $L$ be the largest value of $|\pi(Y; L, r) - M(Y, L)|$ over residues $r$ coprime to $L$ (or $0$ if there are none), and let $\tau_{k+1}(L)$ count ordered factorizations of $L$ into $k+1$ positive factors. Then\n\n$$\sum_{L \leq R^2} \text{fiberWeight}(i, L) \cdot (\text{err}(Y_1, L) + \text{err}(Y_2, L)) \leq \sum_{L \leq R^2} \tau_{k+1}(L)^2 \text{err}(Y_1, L) + \sum_{L \leq R^2} \tau_{k+1}(L)^2 \text{err}(Y_2, L).$$\n\nThis is the bridge from fiber weights to divisor weights: termwise, the Selberg fiber weight is at most $\tau_{k+1}(L)^2$ by the Selberg fiber bound, and the errors are nonnegative. Formalization Note: the support set, the good-pair condition, the Selberg weight, the divisor count, and the max coprime-residue error are all unfolded into explicit finite sums, filters, and cardinalities.
-- source:
--   GPY divisor-weighted BV estimate: the fiber-weighted error sum at one coordinate is at most the sum of the two divisor-weighted endpoint sums, from the Selberg fiber bound termwise

import Mathlib
open Classical

theorem gpy_fiberWeight_sum_le_divWeightedErrSum {k : ℕ} (h : Fin k → ℕ)
    (R deg : ℕ) (hR : 2 ≤ R) (M : ℕ → ℕ → ℝ) (i : Fin k) (Y₁ Y₂ : ℕ) :
    ∑ L ∈ Finset.range (R ^ 2 + 1),
        (∑ p ∈ (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R)) ×ˢ
            ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R))).filter
          (fun p => (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
              Nat.Coprime (w + h i)
                (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
            Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
          abs ((if ∏ i, p.1 i ≤ R then
                (ArithmeticFunction.moebius (∏ i, p.1 i) : ℝ)
                  * (1 - Real.log ((∏ i, p.1 i : ℕ) : ℝ) / Real.log R) ^ deg
                else 0)
              * (if ∏ i, p.2 i ≤ R then
                (ArithmeticFunction.moebius (∏ i, p.2 i) : ℝ)
                  * (1 - Real.log ((∏ i, p.2 i : ℕ) : ℝ) / Real.log R) ^ deg
                else 0)))
          * ((if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (Y₁ + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y₁ L))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (Y₁ + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y₁ L))).max' hne
              else 0)
            + (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (Y₂ + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y₂ L))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (Y₂ + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y₂ L))).max' hne
              else 0))
      ≤ (∑ L ∈ Finset.range (R ^ 2 + 1),
          (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
            (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
            * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (Y₁ + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y₁ L))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (Y₁ + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y₁ L))).max' hne
              else 0))
        + (∑ L ∈ Finset.range (R ^ 2 + 1),
          (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
            (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
            * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (Y₂ + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y₂ L))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (Y₂ + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y₂ L))).max' hne
              else 0)) := by sorry
