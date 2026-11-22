-- Prove2me | Theorems.Thm_mBound_pos
-- name    : mBound_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:36.435043+00:00
-- url     : https://prove2.me/theorems/f0d5962a-49d5-4557-b2e9-253e1aa9039d
-- title:
--   m Bound pos: m Bound pos
-- statement:
--   The m Bound pos construction uses the m Bound pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L358-L359
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L358-L359

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

theorem mBound_pos {k : ℕ} (hk : k ≠ 0) : 0 < mBound k := by sorry
