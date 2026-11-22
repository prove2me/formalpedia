-- Prove2me | Theorems.Thm_nonempty_of_uniformOn_apply_pos
-- name    : nonempty_of_uniformOn_apply_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:37:39.862464+00:00
-- url     : https://prove2.me/theorems/257d59a1-ce75-4f15-af1c-4cd05f184a92
-- title:
--   nonempty of uniform On apply pos: nonempty of uniform On apply pos
-- statement:
--   The nonempty of uniform On apply pos construction uses the nonempty of uniform On apply pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L142-L146
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L142-L146

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
import Definitions.Def_Polychromatic_Existence
set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory

theorem nonempty_of_uniformOn_apply_pos {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {s t : Set Ω} (h : 0 < uniformOn s t) :
    (s ∩ t).Nonempty := by sorry
