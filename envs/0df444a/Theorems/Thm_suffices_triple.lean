-- Prove2me | Theorems.Thm_suffices_triple
-- name    : suffices_triple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:47:21.672651+00:00
-- url     : https://prove2.me/theorems/a90d981c-798a-44e4-bb10-f3e0e97c873e
-- title:
--   suffices triple: suffices triple
-- statement:
--   It suffices to verify all ordered triples `0 < a < b < c`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L55-L73
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L55-L73

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

theorem suffices_triple
    (h : ∀ a b c : ℤ, 0 < a → a < b → b < c → HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ S : Finset ℤ, #S = 4 → Minimal (· ∈ S) 0 → HasPolychromColouring (Fin 3) S := by sorry
