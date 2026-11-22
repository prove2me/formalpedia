-- Prove2me | Theorems.Thm_suffices_nat
-- name    : suffices_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:16.787188+00:00
-- url     : https://prove2.me/theorems/dd99b94d-3436-4a6b-8eb6-de09d8a49f59
-- title:
--   suffices nat: suffices nat
-- statement:
--   The suffices nat construction uses the suffices nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L163-L172
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L163-L172

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory
set_option autoImplicit true
open Finset

theorem suffices_nat (C : ℕ) (h : allC C) :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → c < C → Finset.gcd {a, b, c} id = 1 →
      HasPolychromColouring (Fin 3) {0, a, b, c} := by sorry
