-- Prove2me | Theorems.Thm_suffices_minimal
-- name    : suffices_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:47:21.541186+00:00
-- url     : https://prove2.me/theorems/e6920e46-3840-44c0-90d5-6bc454825e9c
-- title:
--   suffices minimal: suffices minimal
-- statement:
--   It suffices to prove the result for sets with minimal element 0.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L49-L52
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L49-L52

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

theorem suffices_minimal
    (h : ∀ S : Finset ℤ, #S = 4 → Minimal (· ∈ S) 0 → HasPolychromColouring (Fin 3) S):
    ∀ S : Finset ℤ, #S = 4 → HasPolychromColouring (Fin 3) S := by sorry
