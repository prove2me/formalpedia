-- Prove2me | Theorems.Thm_gpy_singSum_selberg_cond_eval
-- name    : gpy_singSum_selberg_cond_eval
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:34:06.31402+00:00
-- url     : https://prove2.me/theorems/c1f71d4a-19ff-48a5-b6e8-ff258011c0e0
-- title:
--   Conditional evaluation of the Selberg singular sum from per-monomial evaluations
-- statement:
--   Let $h$ be a tuple of shifts, let $R$ be a level, let $\deg$ be a degree, and let $i$ be a coordinate. Let $\lambda$ be the Selberg weight of degree $\deg$ and let the singular sum be the sum over good support pairs of $\lambda_d \lambda_e / \varphi(L(d, e))$. Suppose that for every pair of monomial indices $a, b \leq \deg$, the monomial pair sum is evaluated by a main term $\mathrm{main}(a, b)$ with error at most $\mathrm{err}(a, b)$: $|\text{monomial}(a, b) - \mathrm{main}(a, b)| \leq \mathrm{err}(a, b)$. This hypothesis is the per-monomial Mertens evaluation; it is assumed here, not proved. Then the singular sum is evaluated by the corresponding binomial combination of the main terms, with error at most the binomial combination of the errors:
--
--   $$\left| \text{singular sum} - \sum_{a, b \leq \deg} \binom{\deg}{a}\binom{\deg}{b} \mathrm{main}(a, b) \right| \leq \sum_{a, b \leq \deg} \binom{\deg}{a}\binom{\deg}{b} \mathrm{err}(a, b).$$
--
--   This is the assembly step only: it transfers per-monomial evaluations to the singular sum by the exact monomial expansion and the triangle inequality, and it does not discharge the per-monomial hypothesis. Formalization Note: the support set, the good-pair condition, the Selberg weight, and the monomial sums are all unfolded into explicit finite sums and filters.
-- source:
--   GPY conditional monomial evaluation: conditional assembly of the Selberg singular sum from per-monomial evaluations, via the monomial expansion and the triangle inequality

import Mathlib
open Classical

theorem gpy_singSum_selberg_cond_eval {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) (mainMono : ℕ → ℕ → ℝ) (errMono : ℕ → ℕ → ℝ)
    (hMono : ∀ a ∈ Finset.range (deg + 1), ∀ b ∈ Finset.range (deg + 1),
      abs ((∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
        then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
            * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
            * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
            * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
            / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
        else 0) - mainMono a b) ≤ errMono a b) :
    abs ((∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
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
        - ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
            (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono a b)
      ≤ ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
          (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono a b := by sorry
