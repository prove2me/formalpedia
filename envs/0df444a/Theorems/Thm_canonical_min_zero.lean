-- Prove2me | Theorems.Thm_canonical_min_zero
-- name    : canonical_min_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:44.967003+00:00
-- url     : https://prove2.me/theorems/3a0aa417-0796-4368-85c1-383bb6ba878f
-- title:
--   canonical min zero: canonical min zero
-- statement:
--   The canonical min zero construction uses the canonical min zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L218-L231
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L218-L231

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset

theorem canonical_min_zero {n : ℕ} (hn : n ≠ 0)
    (h : ∀ S : Finset ℤ, #S = n → Minimal (· ∈ S) 0 → HasPolychromColouring K S) :
    ∀ S : Finset ℤ, #S = n → HasPolychromColouring K S := by sorry
