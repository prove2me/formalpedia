-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_bernoulli_signed_mgf
-- name    : ZeroFreeRRG.Hardcore.bernoulli_signed_mgf
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:31:56.973664+00:00
-- url     : https://prove2.me/theorems/f9d9cde2-71ad-4147-8d8f-b47fa69ee08d
-- title:
--   Bernoulli signed-variable exponential moment
-- statement:
--   For $s\in[0,1]$, $0\le\theta\le1/3$, and $|z|\le1$, the centered Bernoulli exponential moment satisfies $$(1-s+s e^{\theta z})e^{-s\theta z}\le e^{3s\theta^2/4}.$$
-- source:
--   Auxiliary Bernstein-inequality ingredient for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.bernoulli_signed_mgf (s θ z : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/3) (hz : |z| ≤ 1) :
    (1-s+s*Real.exp (θ*z))*Real.exp (-(s*θ*z)) ≤ Real.exp ((3/4)*s*θ^2) := by sorry
