-- Prove2me | Theorems.Thm_suffices_flip
-- name    : suffices_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:47:53.667697+00:00
-- url     : https://prove2.me/theorems/e3898511-6854-4e23-8eca-6c826a30a8d0
-- title:
--   suffices flip: suffices flip
-- statement:
--   The "flip" reduction: if `a + b > c`, we can replace `{0, a, b, c}` with
--   `{0, c-b, c-a, c}`, which satisfies `(c-b) + (c-a) ≤ c` (since `a + b > c`).
--   This uses translation and negation invariance of the polychromatic number.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L78-L91
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L78-L91

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

theorem suffices_flip
    (h : ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c →
      HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ a b c : ℤ, 0 < a → a < b → b < c → HasPolychromColouring (Fin 3) {0, a, b, c} := by sorry
