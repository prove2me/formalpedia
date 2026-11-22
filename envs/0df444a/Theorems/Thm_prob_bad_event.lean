-- Prove2me | Theorems.Thm_prob_bad_event
-- name    : prob_bad_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:37:31.121326+00:00
-- url     : https://prove2.me/theorems/932b69c8-1128-4319-bc00-11b449139e91
-- title:
--   prob bad event: prob bad event
-- statement:
--   The prob bad event construction uses the prob bad event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L85-L118
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean#L85-L118

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

theorem prob_bad_event [DecidableEq G] {k m : ℕ} {S X : Finset G} {x : X} (hm : #S = m) (hk : k ≠ 0) :
    (Measure.pi (fun _ ↦ uniformOn Set.univ) : Measure (X + S → Fin k)).real
      {χ : X + S → Fin k | ∃ c, ∀ s : S, χ ⟨x + s, add_mem_add x.2 s.2⟩ ≠ c} ≤
        k * (1 - (k : ℝ)⁻¹) ^ m := by sorry
