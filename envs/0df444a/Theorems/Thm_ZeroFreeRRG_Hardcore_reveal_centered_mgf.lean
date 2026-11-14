-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_centered_mgf
-- name    : ZeroFreeRRG.Hardcore.reveal_centered_mgf
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:33:12.564381+00:00
-- url     : https://prove2.me/theorems/418fa796-825d-4ed4-a43e-a2e2b87c6f1e
-- title:
--   Centered moment-generating bound for Bernoulli reveal sets
-- statement:
--   For independent Bernoulli($s$) vertex revelations, coefficients $|z_v|\le1$, and $0\le\theta\le1/3$, the exponential moment of the centered revealed sum is bounded by $e^{3s\theta^2n/4}$.
-- source:
--   Auxiliary Bernstein-inequality ingredient for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.reveal_centered_mgf (n : ℕ) (s θ : ℝ) (z : Fin n → ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/3)
    (hz : ∀ v, |z v| ≤ 1) :
    (∑ U : Finset (Fin n), revealProb s U *
      Real.exp (θ * ((∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)))) ≤
        Real.exp ((3/4)*s*θ^2*n) := by sorry
