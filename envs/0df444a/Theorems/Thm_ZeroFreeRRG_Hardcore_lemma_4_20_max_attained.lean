-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_max_attained
-- name    : ZeroFreeRRG.Hardcore.lemma_4_20_max_attained
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:51:15.183933+00:00
-- url     : https://prove2.me/theorems/5e66cfae-3ee1-4470-92ca-2f685359e0e2
-- title:
--   The perturbed Bethe variational maximum is attained
-- statement:
--   For either valid positive-parameter model, every integer degree, and every real reveal parameter $s$, the Bethe functional plus the reveal perturbation in equation (29) attains a maximum on the cavity-law domain.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 31, Lemma 4.20, equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open Set Filter MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.lemma_4_20_max_attained (m : Model) (hm : m.Valid) (d : ℕ) (t : ℝ) (ht : m.PosParam t) (s : ℝ) :
    ∃ ν₀ ∈ cavityLaws m t, ∀ ν ∈ cavityLaws m t,
      betheK m t d ν + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
          ∂(ν : Measure (m.Spin → ℝ)) ≤
      betheK m t d ν₀ + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
          ∂(ν₀ : Measure (m.Spin → ℝ)) := by sorry
