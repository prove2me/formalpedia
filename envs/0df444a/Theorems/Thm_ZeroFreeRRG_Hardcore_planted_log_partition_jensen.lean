-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_planted_log_partition_jensen
-- name    : ZeroFreeRRG.Hardcore.planted_log_partition_jensen
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:54:27.3517+00:00
-- url     : https://prove2.me/theorems/1797fa3c-5981-48cb-9699-9446cc5a9722
-- title:
--   Planted expected log partition exceeds log first moment
-- statement:
--   For every valid positive-parameter model and nonempty configuration matching space, the planted expectation of the log normalized partition function is at least the logarithm of its configuration-model first moment. This holds for every reveal parameter because the reveal-set weights sum to one.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 31 and Appendix E.3, Lemma 4.20.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.planted_log_partition_jensen (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t) (d n : ℕ)
    [Nonempty (Matching n d)] :
    Real.log (an m d n t) ≤ plantedPinnedE m t s d n (fun M _ _ => Real.log (normZ m t M)) := by sorry
