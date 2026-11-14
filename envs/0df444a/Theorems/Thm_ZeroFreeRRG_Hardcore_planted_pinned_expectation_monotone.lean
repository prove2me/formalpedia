-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_planted_pinned_expectation_monotone
-- name    : ZeroFreeRRG.Hardcore.planted_pinned_expectation_monotone
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:01:09.990531+00:00
-- url     : https://prove2.me/theorems/1690fbc0-4b8a-4b2c-baa3-b8a66dd9ae45
-- title:
--   Monotonicity of planted reveal expectation
-- statement:
--   For nonnegative spin and edge marginals and a reveal probability in the unit interval, the planted reveal expectation preserves pointwise inequalities.
-- source:
--   Auxiliary probabilistic step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.planted_pinned_expectation_monotone (m : Model) (t s : ℝ) (d n : ℕ)
    (hπ : ∀ a, 0 ≤ m.pi t a) (hP : ∀ a b, 0 ≤ m.P t a b) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (f g : Matching n d → (Fin n → m.Spin) → Finset (Fin n) → ℝ)
    (hfg : ∀ M σ U, f M σ U ≤ g M σ U) :
    plantedPinnedE m t s d n f ≤ plantedPinnedE m t s d n g := by sorry
