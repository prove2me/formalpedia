-- Prove2me | Theorems.Thm_mBound_le_helper
-- name    : mBound_le_helper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:10.515797+00:00
-- url     : https://prove2.me/theorems/282b808c-40b1-4d08-b2bd-b444d847e133
-- title:
--   m Bound le helper: m Bound le helper
-- statement:
--   The m Bound le helper construction uses the m Bound le helper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L365-L374
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L365-L374

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

theorem mBound_le_helper {k : ℕ} :
    mBound k ≤ k * (3 * log k + (2 * log (log k) + 6.2)) := by sorry
