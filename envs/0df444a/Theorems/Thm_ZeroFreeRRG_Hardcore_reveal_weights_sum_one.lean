-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_weights_sum_one
-- name    : ZeroFreeRRG.Hardcore.reveal_weights_sum_one
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:03:56.035979+00:00
-- url     : https://prove2.me/theorems/bb05a3ad-4bba-4929-ac61-5e0068dcb92a
-- title:
--   Bernoulli reveal-set weights sum to one
-- statement:
--   For every finite vertex set of size $n$ and every real $s$, the sum over all reveal sets $U$ of $s^{|U|}(1-s)^{n-|U|}$ equals one. For $s\in[0,1]$ these are the Bernoulli reveal-set probabilities used in the planted-overlap argument.
-- source:
--   Auxiliary probabilistic identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, §4.3 and p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.reveal_weights_sum_one (n : ℕ) (s : ℝ) :
    (∑ U : Finset (Fin n), revealProb s U) = 1 := by sorry
