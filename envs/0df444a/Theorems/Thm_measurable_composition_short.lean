-- Prove2me | Theorems.Thm_measurable_composition_short
-- name    : measurable_composition_short
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:51:59.349165+00:00
-- url     : https://prove2.me/theorems/987e72ba-01fb-4974-9db1-0cbd9465d395
-- title:
--   04_thm_4_3: measurable_composition_short
-- statement:
--   Original source theorem `measurable_composition_short` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_3.lean

import Mathlib.MeasureTheory.MeasurableSpace.Basic
section Theorem_4_3
variable {Ω Ω' Ω'' : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']

theorem measurable_composition_short {f : Ω → Ω'} {g : Ω' → Ω''}
    (hf : Measurable f) (hg : Measurable g) : Measurable (g ∘ f) := by
  sorry
end Theorem_4_3
