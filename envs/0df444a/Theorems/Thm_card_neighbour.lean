-- Prove2me | Theorems.Thm_card_neighbour
-- name    : card_neighbour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:37:28.509076+00:00
-- url     : https://prove2.me/theorems/0efc717e-3639-4e0a-a079-142b5565ef15
-- title:
--   card neighbour: card neighbour
-- statement:
--   The card neighbour construction uses the card neighbour property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L120-L133
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L120-L133

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

theorem card_neighbour [DecidableEq G] {m : ℕ} {S X : Finset G} (hm : #S = m) {x : X} :
    #(X.attach.filter (fun i ↦ x.1 - i.1 ∈ (S - S).erase 0)) ≤ m * (m - 1) := by sorry
