-- Prove2me | Theorems.Thm_linear_le_mBound
-- name    : linear_le_mBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:55.269843+00:00
-- url     : https://prove2.me/theorems/785fd7f4-3e29-47fe-a55c-7cdea03df0a0
-- title:
--   linear le m Bound: linear le m Bound
-- statement:
--   The linear le m Bound construction uses the linear le m Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L349-L356
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L349-L356

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

theorem linear_le_mBound {k : ℕ} : 2 * k ≤ mBound k := by sorry
