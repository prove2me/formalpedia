-- Prove2me | Theorems.Thm_exists_finite_of_le
-- name    : exists_finite_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:37:37.691899+00:00
-- url     : https://prove2.me/theorems/a1296168-54c4-49c1-9c27-8d8dd812a31b
-- title:
--   exists finite of le: exists finite of le
-- statement:
--   The exists finite of le construction uses the exists finite of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L153-L194
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L153-L194

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

theorem exists_finite_of_le [DecidableEq G] {k m : ℕ} (X : Finset G) {S : Finset G} (hm : #S = m)
    (hm₂ : 2 ≤ m) (hk : k ≠ 0) (hkm : polychromColouringBound k m) :
    ∃ χ : G → Fin k, ∀ x ∈ X, ∀ c : Fin k, ∃ i ∈ x +ᵥ S, χ i = c := by sorry
