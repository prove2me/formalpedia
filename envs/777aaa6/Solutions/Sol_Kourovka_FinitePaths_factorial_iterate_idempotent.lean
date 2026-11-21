-- Prove2me | solution 1 for Kourovka.FinitePaths.factorial_iterate_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:31:38.413169+00:00
-- url     : https://prove2.me/submissions/a8fd8cc8-dc12-4df4-893c-dcdb3f724b05

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_FinitePaths

set_option autoImplicit true
open Kourovka
open Kourovka.FinitePaths
namespace Kourovka.FinitePaths
theorem _root_.solution {X : Type*} [Fintype X]
    (f : X → X) (b : ℕ) (hcard : Fintype.card X ≤ b) :
    f^[2 * b.factorial] = f^[b.factorial] := by
  funext x
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (b + 1) => f^[i.val] x)
    (by simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hcard)
  have hpair : ∃ a c : ℕ, a < c ∧ c ≤ b ∧ f^[a] x = f^[c] x := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i.val, j.val, hlt, Nat.le_of_lt_succ j.isLt, heq⟩
    · exact ⟨j.val, i.val, hgt, Nat.le_of_lt_succ i.isLt, heq.symm⟩
  obtain ⟨a, c, hac, hcb, heq⟩ := hpair
  let d := c - a
  have hd : 0 < d := Nat.sub_pos_of_lt hac
  have hdb : d ≤ b := (Nat.sub_le c a).trans hcb
  have hperiod : ∀ n, a ≤ n → f^[n + d] x = f^[n] x := by
    intro n hn
    calc
      f^[n + d] x = f^[(n - a) + c] x := by congr 1; omega
      _ = f^[n - a] (f^[c] x) := Function.iterate_add_apply _ _ _ _
      _ = f^[n - a] (f^[a] x) := by rw [← heq]
      _ = f^[(n - a) + a] x := (Function.iterate_add_apply _ _ _ _).symm
      _ = f^[n] x := by rw [Nat.sub_add_cancel hn]
  have hmultiple : ∀ k n, a ≤ n → f^[n + k * d] x = f^[n] x := by
    intro k
    induction k with
    | zero => intro n hn; simp
    | succ k ih =>
      intro n hn
      rw [Nat.succ_mul, ← Nat.add_assoc, hperiod (n + k * d) (by omega), ih n hn]
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hd hdb
  have ham : a ≤ b.factorial := (Nat.le_of_lt hac).trans (hcb.trans (Nat.self_le_factorial b))
  have hfin := hmultiple k b.factorial ham
  simpa only [Nat.mul_comm k d, ← hk, two_mul] using hfin
end Kourovka.FinitePaths
