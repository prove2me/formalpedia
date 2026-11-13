-- Prove2me | Theorems.Thm_extension_unique
-- name    : extension_unique
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T21:56:34.672012+00:00
-- url     : https://prove2.me/theorems/01ee8ada-60ea-4408-bd0b-2f1fbef95a08
-- title:
--   Chapter 3, thm_3_8: extension_unique
-- statement:
--   Source theorem `extension_unique` from Chapter 3, module `thm_3_8`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_8.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_2_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_3_F000
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Tactic

universe u

open MeasureTheory Set ENNReal MeasurableSpace

theorem extension_unique {X : Type u} (F₀ : FieldOfSets X) (pm : Premeasure F₀)
    (h_sigma_finite : IsSigmaFinite pm) :
    ∃! μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
      IsExtension F₀.carrier pm.toSetFunction μ := by sorry
