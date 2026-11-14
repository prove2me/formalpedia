-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_two_sided_bernstein
-- name    : ZeroFreeRRG.Hardcore.reveal_two_sided_bernstein
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:35:29.768204+00:00
-- url     : https://prove2.me/theorems/7c588054-8944-4860-b641-45e27d609f31
-- title:
--   Two-sided Bernstein bound for revealed signed sums
-- statement:
--   For independent Bernoulli($s$) vertex revelations and coefficients $|z_v|\le1$, the probability that the absolute centered revealed sum is at least $s\eta n/2$ is at most $2e^{-s\eta^2 n/12}$ for $0<\eta\le1$.
-- source:
--   Auxiliary Bernstein inequality for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.reveal_two_sided_bernstein (n : ℕ) (s η : ℝ) (z : Fin n → ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hz : ∀ v, |z v| ≤ 1) :
    (∑ U : Finset (Fin n), revealProb s U *
      (if s*η*n/2 ≤ |(∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)| then 1 else 0)) ≤
        2*Real.exp (-(s*η^2/12)*n) := by sorry
