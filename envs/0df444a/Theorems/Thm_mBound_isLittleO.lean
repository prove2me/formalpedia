-- Prove2me | Theorems.Thm_mBound_isLittleO
-- name    : mBound_isLittleO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:14.754178+00:00
-- url     : https://prove2.me/theorems/b7ab8067-3858-4934-b581-20cb83d7351b
-- title:
--   m Bound is Little O: m Bound is Little O
-- statement:
--   The m Bound is Little O construction uses the m Bound is Little O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L412-L426
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L412-L426

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
open Asymptotics Filter Topology

theorem mBound_isLittleO :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧ ∀ k ≥ 2, mBound k ≤ (3 + f k) * k * log k := by sorry
