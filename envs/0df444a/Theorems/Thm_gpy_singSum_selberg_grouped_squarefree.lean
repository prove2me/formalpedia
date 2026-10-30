-- Prove2me | Theorems.Thm_gpy_singSum_selberg_grouped_squarefree
-- name    : gpy_singSum_selberg_grouped_squarefree
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:24:41.811825+00:00
-- url     : https://prove2.me/theorems/c88b2e90-9d14-473f-8a76-4d70c89237c6
-- title:
--   Selberg singular sum grouped over squarefree moduli only
-- statement:
--   Let $h$ be a tuple of shifts, let $R$ be a level, let $\deg$ be a degree, and let $i$ be a coordinate. Let $\lambda_d = \mu(\prod d)(1 - \log \prod d / \log R)^{\deg}$ when $\prod d \leq R$ (and $0$ otherwise) be the Selberg weight, and let the singular sum be the sum over good support pairs $(d, e)$ of $\lambda_d \lambda_e / \varphi(L(d, e))$, where goodness at $i$ is the witness condition and $L(d, e)$ is the combined modulus. Then the singular sum equals the sum over monomial indices $a, b \leq \deg$ of $\binom{\deg}{a}\binom{\deg}{b}$ times the sum over squarefree moduli $L$ in $[1, R^2]$ of $(1/\varphi(L))$ times the monomial piece at exact modulus $L$. The restriction to squarefree $L$ loses nothing, since the monomial piece at a non-squarefree modulus vanishes by Möbius. This is the form in which the evaluation must be proved: on squarefree $L$, the combined modulus equals $\mathrm{lcm}(\prod d, \prod e)$. The full evaluation of the singular sum to the singular series times an integral is not claimed here. Formalization Note: the support set, the good-pair condition, and the Selberg weight are all unfolded into explicit finite sums and filters.
-- source:
--   GPY conditional monomial evaluation: the Selberg singular sum in grouped form over squarefree moduli only, from the grouped form and the vanishing of non-squarefree pieces

import Mathlib
open Classical

theorem gpy_singSum_selberg_grouped_squarefree {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
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
          ∑ L ∈ (Finset.Icc 1 (R ^ 2)).filter (fun L => Squarefree L),
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
