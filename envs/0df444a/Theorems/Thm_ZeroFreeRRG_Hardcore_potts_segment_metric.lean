-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_segment_metric
-- name    : ZeroFreeRRG.Hardcore.potts_segment_metric
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:11:25.51505+00:00
-- url     : https://prove2.me/theorems/f0a055c2-57cc-436d-a106-7d6115850c93
-- title:
--   Metric bounds for two points on a complex segment
-- statement:
--   For two points on the segment from $1$ to $\beta$, their distance is at most $|\beta-1|$, and each has modulus at least $1-|\beta-1|$.
-- source:
--   Auxiliary phase bound for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_segment_metric (β : ℂ) (s t : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖(1+(t:ℂ)*(β-1))-(1+(s:ℂ)*(β-1))‖ ≤ ‖β-1‖ ∧
      1-‖β-1‖ ≤ ‖1+(s:ℂ)*(β-1)‖ := by sorry
