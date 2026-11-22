-- Prove2me | Theorems.Thm_indepFun_restrict_restrict_pi
-- name    : indepFun_restrict_restrict_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:34:39.091647+00:00
-- url     : https://prove2.me/theorems/40e686c3-f22f-4d83-be40-1b2917e715c3
-- title:
--   indep Fun restrict restrict pi: indep Fun restrict restrict pi
-- statement:
--   The indep Fun restrict restrict pi construction uses the indep Fun restrict restrict pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L111-L118
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L111-L118

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset
open MeasureTheory Measure ProbabilityTheory
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}
variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}

theorem indepFun_restrict_restrict_pi {s t : Set ι} (hi : Disjoint s t) :
    IndepFun s.restrict t.restrict (Measure.pi P) := by sorry
