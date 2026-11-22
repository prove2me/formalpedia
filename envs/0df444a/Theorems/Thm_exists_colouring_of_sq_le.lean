-- Prove2me | Theorems.Thm_exists_colouring_of_sq_le
-- name    : exists_colouring_of_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:58.612652+00:00
-- url     : https://prove2.me/theorems/6e4bc61d-1bfa-4a6b-b7d8-9626db1191db
-- title:
--   exists colouring of sq le: exists colouring of sq le
-- statement:
--   The exists colouring of sq le construction uses the exists colouring of sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L319-L325
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L319-L325

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

theorem exists_colouring_of_sq_le {S : Finset G} {k : ℕ} (hk : k ≠ 0) (hm : 3 * k ^ 2 ≤ #S) :
    HasPolychromColouring (Fin k) S := by sorry
