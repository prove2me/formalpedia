-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_log_first_moment
-- name    : ZeroFreeRRG.Hardcore.lemma_4_20_log_first_moment
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T10:46:40.80021+00:00
-- url     : https://prove2.me/theorems/603a1a23-57aa-4ae6-bc4a-c0ece015898e
-- title:
--   Lemma 4.20: logarithmic first-moment bound
-- statement:
--   For the positive-parameter hardcore and antiferromagnetic Potts models at fixed degree, the absolute logarithm of the configuration-model first moment is at most a constant times log(n+1) for all sufficiently large admissible n.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 31, Lemma 4.20 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
open scoped Classical
open Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore

theorem ZeroFreeRRG.Hardcore.lemma_4_20_log_first_moment (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
        |Real.log (an m d n t)| ≤ C * Real.log (n + 1) := by sorry
