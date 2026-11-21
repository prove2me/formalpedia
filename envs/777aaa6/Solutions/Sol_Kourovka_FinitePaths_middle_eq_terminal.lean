-- Prove2me | solution 1 for Kourovka.FinitePaths.middle_eq_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:18.345319+00:00
-- url     : https://prove2.me/submissions/89b5432c-1f0e-49ec-9d91-1149417e08d3

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_FinitePaths
import Theorems.Thm_Kourovka_FinitePaths_exists_idempotent_iterate

set_option autoImplicit true
open Kourovka
open Kourovka.FinitePaths
namespace Kourovka.FinitePaths
theorem _root_.solution {α : Type*} (X : Set (ℕ → α)) (hX : X.Finite)
    (hs : ∀ x ∈ X, shift x ∈ X) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ X, x m = x (2 * m) := by
  classical
  letI : Fintype X := hX.fintype
  let s : X → X := fun x => ⟨shift x.val, hs x.val x.property⟩
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
  obtain ⟨m, hm, heq⟩ := exists_idempotent_iterate s
  refine ⟨m, hm, ?_⟩
  intro x hx
  have he := congrArg (fun t : X => t.val 0) (congrFun heq ⟨x, hx⟩)
  simpa only [hiter, Nat.zero_add] using he.symm
end Kourovka.FinitePaths
