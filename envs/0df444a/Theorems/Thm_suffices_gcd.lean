-- Prove2me | Theorems.Thm_suffices_gcd
-- name    : suffices_gcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:47:44.30217+00:00
-- url     : https://prove2.me/theorems/838f1c91-d1fc-4975-b269-a7121139f130
-- title:
--   suffices gcd: suffices gcd
-- statement:
--   It suffices to check coprime cases.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L94-L136
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L94-L136

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

theorem suffices_gcd
    (h : ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → Finset.gcd {a, b, c} id = 1 →
      HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c →
      HasPolychromColouring (Fin 3) {0, a, b, c} := by sorry
