-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_log_n_over_n
-- name    : ZeroFreeRRG.Hardcore.log_n_over_n
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:58:46.679831+00:00
-- url     : https://prove2.me/theorems/419010fb-30a0-4ce6-8ba0-9db77408cfd9
-- title:
--   Logarithmic growth divided by n vanishes
-- statement:
--   For every real constant C, the sequence $-C\log(n+1)/n$ tends to zero as $n\to\infty$.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 31, Lemma 4.20, equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter Topology MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.log_n_over_n (C : ℝ) : Tendsto (fun n : ℕ => -C * Real.log ((n:ℝ)+1) / n) atTop (𝓝 0) := by sorry
