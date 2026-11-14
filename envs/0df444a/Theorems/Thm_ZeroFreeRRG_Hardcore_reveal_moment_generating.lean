-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_moment_generating
-- name    : ZeroFreeRRG.Hardcore.reveal_moment_generating
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:32:03.187284+00:00
-- url     : https://prove2.me/theorems/d1837f5b-9e7c-47b8-802a-2b6de38f2cf5
-- title:
--   Bernoulli reveal-set moment generating function
-- statement:
--   For any real coefficients $z_v$ and parameters $s,\theta$, the sum over reveal sets $U$ of their Bernoulli weight times $e^{\theta\sum_{v\in U}z_v}$ equals $\prod_v(1-s+s e^{\theta z_v})$.
-- source:
--   Auxiliary Bernstein-inequality ingredient for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.reveal_moment_generating (n : ℕ) (s θ : ℝ) (z : Fin n → ℝ) :
    (∑ U : Finset (Fin n), revealProb s U * Real.exp (θ * ∑ v ∈ U, z v)) =
      ∏ v : Fin n, (s * Real.exp (θ*z v) + (1-s)) := by sorry
