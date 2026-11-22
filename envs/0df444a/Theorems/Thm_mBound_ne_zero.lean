-- Prove2me | Theorems.Thm_mBound_ne_zero
-- name    : mBound_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:33.78526+00:00
-- url     : https://prove2.me/theorems/84a1e5d1-dddd-40c1-9cec-c7630fe814c9
-- title:
--   m Bound ne zero: m Bound ne zero
-- statement:
--   The m Bound ne zero construction uses the m Bound ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L360-L360
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L360-L360

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

theorem mBound_ne_zero {k : ℕ} (hk : k ≠ 0) : mBound k ≠ 0 := by sorry
