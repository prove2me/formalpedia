-- Prove2me | Theorems.Thm_gpy_secondMoment_divWeightedBV_bound
-- name    : gpy_secondMoment_divWeightedBV_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:23:11.542786+00:00
-- url     : https://prove2.me/theorems/c0c56a7d-c3fd-4ab4-90d5-5cfaf76b8836
-- title:
--   Conditional divisor-weighted BV bound for the GPY second moment
-- statement:
--   Let $h$ be a tuple of shifts, let $R \geq 2$ be a level, let $\deg$ be a degree, let $M$ be a model for prime counts in arithmetic progressions, and let $x \leq y$ be interval endpoints. Let $S_2$ be the GPY second moment with the Selberg weight and let the BV main term be the sum over support pairs of $\lambda_d \lambda_e$ times the model differences at the interval endpoints for good pairs ($0$ for bad pairs). Suppose that for every coordinate $i$, the divisor-weighted error sum at each endpoint — the sum over $L \leq R^2$ of $\tau_{k+1}(L)^2$ times the max coprime-residue error at that endpoint and modulus $L$ — is at most a bound $E$ evaluated at that endpoint. This divisor-weighted hypothesis is assumed here, not proved. Then\n\n$$|S_2 - \text{main term}| \leq \sum_i (E(y + h_i) + E(x + h_i)) + \Lambda \cdot k,$$\n\nwhere $\Lambda$ is the total mass $\sum_{d, e} |\lambda_d \lambda_e|$ over support pairs. This is the conditional assembly: it transfers a divisor-weighted BV estimate at the endpoints into a second-moment error bound, via the grouped error bound and the fiber-weight bridge. Formalization Note: the second moment, the main term, the support set, the good-pair condition, the Selberg weight, the divisor count, and the max coprime-residue error are all unfolded into explicit finite sums, filters, and cardinalities.
-- source:
--   GPY divisor-weighted BV estimate: conditional assembly, under a divisor-weighted BV hypothesis at every endpoint, the second-moment error is at most the sum of the endpoint bounds plus the bad-pair term

import Mathlib
open Classical

theorem gpy_secondMoment_divWeightedBV_bound {k : ℕ} (h : Fin k → ℕ)
    (R deg : ℕ) (hR : 2 ≤ R) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    (E : ℕ → ℝ)
    (hDiv : ∀ i, (∑ L ∈ Finset.range (R ^ 2 + 1),
          (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
            (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
            * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (y + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - M (y + h i) L))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (y + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - M (y + h i) L))).max' hne
              else 0)) ≤ E (y + h i) ∧
      (∑ L ∈ Finset.range (R ^ 2 + 1),
          (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
            (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
            * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (x + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - M (x + h i) L))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (x + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - M (x + h i) L))).max' hne
              else 0)) ≤ E (x + h i)) :
    abs ((∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then
            (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0)
            else 0) ^ 2)
      - (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        (if ∏ i, d i ≤ R then
            (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
              * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          * (if ∏ i, e i ≤ R then
            (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
              * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          * (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i)
                (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            then M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
              - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            else 0)))
      ≤ (∑ i, (E (y + h i) + E (x + h i)))
        + (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          abs ((if ∏ i, d i ≤ R then
                (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                  * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
                else 0)
              * (if ∏ i, e i ≤ R then
                (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                  * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
                else 0))) * (k : ℝ) := by sorry
