-- Prove2me | Theorems.Thm_thm_5_2
-- name    : thm_5_2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:55:42.072901+00:00
-- url     : https://prove2.me/theorems/4b22a238-b62a-4035-a783-14ce08800dd4
-- title:
--   Chapter 5, thm_5_2
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `thm_5_2`: `thm_5_2`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/thm_5_2.lean

import Definitions.Def_ProbabilityTheory_chapter_05_def_5_2_F000
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/--
   ## Theorem 5.2

   Given random variables X and Y are independent,
   f(X) and g(Y) are independent for any measurable functions f and g

-/
theorem thm_5_2 {Ω β γ β' γ' : Type _}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace β'] [MeasurableSpace γ']
    (μ : MeasureTheory.Measure Ω) (X : Ω → β) (Y : Ω → γ)
    (f : β → β') (g : γ → γ')
    (hXY : def_5_2 μ X Y) (hf : Measurable f) (hg : Measurable g) :
    def_5_2 μ (f ∘ X) (g ∘ Y) := by
  sorry
