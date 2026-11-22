-- Prove2me | Theorems.Thm_exists_of_le
-- name    : exists_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:58.97636+00:00
-- url     : https://prove2.me/theorems/5a3b29d5-25fc-4507-b23e-f16a9575d2a2
-- title:
--   exists of le: exists of le
-- statement:
--   The exists of le construction uses the exists of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L200-L217
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L200-L217

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

theorem exists_of_le {k m : ℕ} {S : Finset G} (hm : #S = m) (hm₂ : 2 ≤ m) (hk : k ≠ 0)
    (hkm : polychromColouringBound k m) :
    HasPolychromColouring (Fin k) S := by sorry
