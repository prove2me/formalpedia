-- Prove2me | Theorems.Thm_mBound_one
-- name    : mBound_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:28.758358+00:00
-- url     : https://prove2.me/theorems/db0426dc-2cfe-407a-a8eb-1de95d7eb0a5
-- title:
--   m Bound one: m Bound one
-- statement:
--   The m Bound one construction uses the m Bound one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L342-L342
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L342-L342

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
open Real

theorem mBound_one : mBound 1 = 6 := by sorry
