-- Prove2me | solution 1 for Kourovka.FinitePaths.exists_idempotent_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:32:13.848072+00:00
-- url     : https://prove2.me/submissions/f47f058f-8d85-44a8-bb6b-3aebed81ec06

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_FinitePaths
import Theorems.Thm_Kourovka_FinitePaths_factorial_iterate_idempotent

set_option autoImplicit true
open Kourovka
open Kourovka.FinitePaths
namespace Kourovka.FinitePaths
theorem _root_.solution {X : Type*} [Finite X] (f : X → X) :
    ∃ m : ℕ, 0 < m ∧ f^[2 * m] = f^[m] := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  exact ⟨(Fintype.card X).factorial, Nat.factorial_pos _,
    factorial_iterate_idempotent f (Fintype.card X) le_rfl⟩
end Kourovka.FinitePaths
