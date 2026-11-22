-- Prove2me | Theorems.Thm_dependsOn_mem_iff_exists_preimage
-- name    : dependsOn_mem_iff_exists_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:37:17.990995+00:00
-- url     : https://prove2.me/theorems/8ea14b92-9aaf-4202-ab16-1281c6414b03
-- title:
--   depends On mem iff exists preimage: depends On mem iff exists preimage
-- statement:
--   The depends On mem iff exists preimage construction uses the depends On mem iff exists preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L306-L308
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L306-L308

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset

theorem dependsOn_mem_iff_exists_preimage {α β : Type*} {t : Set α} {A : Set (α → β)} :
    DependsOn (· ∈ A) t ↔ ∃ B : Set (t → β), A = t.restrict ⁻¹' B := by sorry
