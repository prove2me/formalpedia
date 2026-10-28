-- Prove2me | Theorems.Thm_gpy_singSum_expand
-- name    : gpy_singSum_expand
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T19:53:40.911987+00:00
-- url     : https://prove2.me/theorems/d87b4690-6f36-4b9b-9b75-e15cac4ea8c7
-- title:
--   Selberg singular sum: exact monomial-pair decomposition
-- statement:
--   Let h be a tuple of shifts, R a level, deg a degree, and i a coordinate. The Selberg singular sum at i (the sum over good support pairs (d, e) of lam_d * lam_e / phi(L), where lam is the Selberg weight lam_d = mu(prod d) * (1 - log(prod d)/log R)^deg when prod d <= R and 0 otherwise, L is the combined modulus, and a pair is good at i when some witness w of the joint divisibility system has w + h_i coprime to L) equals the exact finite decomposition sum_{a, b <= deg} (deg choose a)(deg choose b) times the (a, b)-monomial pair sum, where the monomial pair sum is the sum over good support pairs of mu(prod d)*mu(prod e) * (-log(prod d)/log R)^a * (-log(prod e)/log R)^b / phi(L). This is the honest replacement for an Euler product: each monomial piece is a Dirichlet-type sum whose evaluation (multinomial prime expansion, Mertens-type estimates, local factors) is the remaining analytic core and is NOT claimed here. This is the ungrouped monomial decomposition, distinct from the grouped forms (by modulus) of the same sum.
-- source:
--   GPY Euler-product analysis: the exact decomposition of the Selberg singular sum into monomial pair sums, via the binomial expansion of the Selberg weight on the support

import Mathlib
open Classical

theorem gpy_singSum_expand {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
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
          (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R),
            ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R),
            if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
                / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
            else 0) := by sorry
