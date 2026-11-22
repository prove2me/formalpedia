-- Prove2me | Theorems.Thm_mBound_le_weak
-- name    : mBound_le_weak
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:38:03.242583+00:00
-- url     : https://prove2.me/theorems/421653fb-0ad9-47b9-8c11-d2cf41376bb0
-- title:
--   m Bound le weak: m Bound le weak
-- statement:
--   The m Bound le weak construction uses the m Bound le weak property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L376-L408
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L376-L408

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

theorem mBound_le_weak {k : ℕ} (hk : 4 ≤ k) : mBound k ≤ 8 * k * log k := by sorry
