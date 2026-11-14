-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_prior_one_sided_bernstein
-- name    : ZeroFreeRRG.Hardcore.reveal_prior_one_sided_bernstein
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:42:44.349335+00:00
-- url     : https://prove2.me/theorems/77a1f6fe-5323-4d14-8b23-5ec3c2b12aed
-- title:
--   Bernstein bound under independently revealed product-prior spins
-- statement:
--   For independent Bernoulli($s$) reveals and independent product-prior spins, if a bounded coefficient has mean zero and absolute value at most one, then its revealed sum exceeds $s\eta n/2$ with probability at most $e^{-s\eta^2n/12}$.
-- source:
--   Auxiliary Bernstein inequality for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.reveal_prior_one_sided_bernstein {A : Type} [Fintype A] (n : ℕ) (s η : ℝ) (ν z : A → ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hν : ∀ a, 0 ≤ ν a) (hνsum : (∑ a, ν a) = 1)
    (hz : ∀ a, |z a| ≤ 1) (hcenter : (∑ a, ν a * z a) = 0) :
    (∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
      (∏ v, ν (y v)) * (if s*η*n/2 ≤ ∑ v, z (y v) then 1 else 0)) ≤
        Real.exp (-(s*η^2/12)*n) := by sorry
