-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_model_has_safe_spin
-- name    : ZeroFreeRRG.Hardcore.model_has_safe_spin
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:01:54.632559+00:00
-- url     : https://prove2.me/theorems/966d8e52-cab2-4819-a25c-554807db756a
-- title:
--   Positive-parameter models have a safe spin
-- statement:
--   For the hardcore and positive-temperature antiferromagnetic Potts models there is a spin $a_0$ whose normalized interaction with every spin is strictly positive. For hardcore one can take the unoccupied spin; for Potts every spin is safe.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, Step 1, p. 77.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.model_has_safe_spin (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) :
    ∃ a₀ : m.Spin, ∀ a : m.Spin, 0 < m.M t a₀ a := by sorry
