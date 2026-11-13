-- Prove2me | Theorems.Thm_measurable_composition
-- name    : measurable_composition
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:51:51.725352+00:00
-- url     : https://prove2.me/theorems/493d5bed-0bca-44ed-bf21-e9e8d410f9e7
-- title:
--   04_thm_4_3: measurable_composition
-- statement:
--   Original source theorem `measurable_composition` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_3.lean

import Mathlib.MeasureTheory.MeasurableSpace.Basic
section Theorem_4_3
variable {Ω Ω' Ω'' : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']

theorem measurable_composition {f : Ω → Ω'} {g : Ω' → Ω''}
    (hf : Measurable f) (hg : Measurable g)
      : Measurable (g ∘ f) := by
  sorry
end Theorem_4_3
