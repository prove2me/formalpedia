-- Prove2me | solution 1 for Kourovka.FinitePaths.factorial_middle_eq_terminal_of_bounded_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:42.703072+00:00
-- url     : https://prove2.me/submissions/b413a4b4-6922-4a6c-b626-9c909b4e4fe6

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_FinitePaths
import Theorems.Thm_Kourovka_FinitePaths_finite_of_bounded_prefixes
import Theorems.Thm_Kourovka_FinitePaths_ncard_le_of_bounded_prefixes
import Theorems.Thm_Kourovka_FinitePaths_factorial_iterate_idempotent

set_option autoImplicit true
open Kourovka
open Kourovka.FinitePaths
namespace Kourovka.FinitePaths
theorem _root_.solution {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b)
    (hs : ∀ x ∈ X, shift x ∈ X) :
    ∀ x ∈ X, x b.factorial = x (2 * b.factorial) := by
  classical
  letI : Fintype X := (finite_of_bounded_prefixes X b hb).fintype
  let s : X → X := fun x => ⟨shift x.val, hs x.val x.property⟩
  have hcard : Fintype.card X ≤ b := by
    simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using
      ncard_le_of_bounded_prefixes X b hb
  have hiter : ∀ n (x : X) k, ((s^[n]) x).val k = x.val (k + n) := by
    intro n
    induction n with
    | zero => intro x k; rfl
    | succ n ih =>
      intro x k
      rw [Function.iterate_succ_apply']
      change ((s^[n]) x).val (k + 1) = x.val (k + (n + 1))
      rw [ih]
      exact congrArg x.val (by omega)
  intro x hx
  have he := congrArg (fun t : X => t.val 0)
    (congrFun (factorial_iterate_idempotent s b hcard) ⟨x, hx⟩)
  simpa only [hiter, Nat.zero_add] using he.symm
end Kourovka.FinitePaths
