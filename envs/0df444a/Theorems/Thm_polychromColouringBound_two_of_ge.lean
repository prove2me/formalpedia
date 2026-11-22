-- Prove2me | Theorems.Thm_polychromColouringBound_two_of_ge
-- name    : polychromColouringBound_two_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:37:54.669177+00:00
-- url     : https://prove2.me/theorems/7e8bb2b3-0072-4857-9fbb-f2d715dc9bc5
-- title:
--   polychrom Colouring Bound two of ge: polychrom Colouring Bound two of ge
-- statement:
--   The polychrom Colouring Bound two of ge construction uses the polychrom Colouring Bound two of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L271-L274
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L271-L274

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

theorem polychromColouringBound_two_of_ge {m : ℕ} (hm : 9 ≤ m) : polychromColouringBound 2 m := by sorry
