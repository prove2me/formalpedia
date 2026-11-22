-- Prove2me | Theorems.Thm_condition_of_mul_sq
-- name    : condition_of_mul_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:37:47.272329+00:00
-- url     : https://prove2.me/theorems/6c931dba-fb39-4458-af17-47bd8b14ca60
-- title:
--   condition of mul sq: condition of mul sq
-- statement:
--   The condition of mul sq construction uses the condition of mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L276-L315
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L276-L315

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

theorem condition_of_mul_sq {k m : ℕ} (hm : 3 * k ^ 2 ≤ m) :
    polychromColouringBound k m := by sorry
