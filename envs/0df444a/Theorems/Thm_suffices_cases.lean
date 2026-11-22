-- Prove2me | Theorems.Thm_suffices_cases
-- name    : suffices_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:21.814281+00:00
-- url     : https://prove2.me/theorems/ec55f231-c52c-43b8-af4e-767d26146694
-- title:
--   suffices cases: suffices cases
-- statement:
--   The suffices cases construction uses the suffices cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L138-L144
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L138-L144

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

theorem suffices_cases (C : ℕ)
    (h₁ : ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → c < C → Finset.gcd {a, b, c} id = 1 →
      HasPolychromColouring (Fin 3) {0, a, b, c})
    (h₂ : ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → C ≤ c → Finset.gcd {a, b, c} id = 1 →
      HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → Finset.gcd {a, b, c} id = 1 →
      HasPolychromColouring (Fin 3) {0, a, b, c} := by sorry
