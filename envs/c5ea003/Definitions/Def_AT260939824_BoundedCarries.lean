-- Prove2me | Definitions.Def_AT260939824_BoundedCarries
-- name    : AT260939824_BoundedCarries
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:42:53.977779+00:00
-- url     : https://prove2.me/theorems/64993380-9e69-46fa-b011-1f35b4233e42
-- title:
--   Elementary word moves and the carry-length budget
-- statement:
--   For a natural-number base $m$, words use letters $a,t,t^{-1}$. Elementary cell moves impose $tat^{-1}=a^m$, the two inverse cancellations, and reversal of a move. The word operators append powers of $a$ and conjugate a word by $t$.
--
--   For $m\ge2$, the selected quotient-and-remainder identities describe incrementing the exponent with and without a carry. Appending $a$ to the compressed word for $n$ has length at most
--
--   $$(m+1)(\lfloor\log_m(n+1)\rfloor+1)+m+3.$$
--
--   These definitions and arithmetic bounds supply the local word data for quantitative carrier paths.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/BoundedCarries.lean, selected declaration lines 16-17, 19-23, 92-95, 97-98, 100, 102-107, 109-116, 118-126; SHA-256 b107f07f38183d0e772f5868f19d231138079aa9d5c01e0147596c2d48983486. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CompressedWords
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Bounded cellular moves on compressed words

The relation records actual presentation-cell moves and backtrack
cancellations in word contexts. Its length index bounds every word in
the finite sequence. This is stronger than equality after evaluation in
the Baumslag--Solitar group.
-/

namespace AbelianTargets

def aWord (n : ℕ) : List BSLetter := List.replicate n BSLetter.a
def conjugateWord (w : List BSLetter) : List BSLetter := [BSLetter.t] ++ w ++ [BSLetter.tInv]

inductive BSCellMove (m : ℕ) : List BSLetter → List BSLetter → Prop
  | relation : BSCellMove m [BSLetter.t,BSLetter.a,BSLetter.tInv] (aWord m)
  | cancelDownUp : BSCellMove m [BSLetter.tInv,BSLetter.t] []
  | cancelUpDown : BSCellMove m [BSLetter.t,BSLetter.tInv] []
  | symm {w z} : BSCellMove m w z → BSCellMove m z w















theorem compressedWord_conjugate (m : ℕ) (hm : 2 ≤ m) {n : ℕ} (hn : m ≤ n) :
    compressedWord m hm n = conjugateWord (compressedWord m hm (n/m)) ++ aWord (n%m) := by
  rw [compressedWord_of_ge m hm hn]
  simp only [conjugateWord, aWord, List.cons_append, List.nil_append, List.append_assoc]

theorem aWord_succ (n : ℕ) : aWord (n+1) = aWord n ++ [BSLetter.a] := by
  simp only [aWord, List.replicate_add, List.replicate_one]

def carryLengthBound (m n : ℕ) : ℕ := (m+1)*(Nat.log m (n+1)+1)+m+3

theorem compressedWord_append_a_length_le (m : ℕ) (hm : 2 ≤ m) (n : ℕ) :
    (compressedWord m hm n ++ [BSLetter.a]).length ≤ carryLengthBound m n := by
  have hlen := compressedWord_interval_uniform_length m hm (n+1) n (by omega)
  simp only [List.length_append, List.length_cons, List.length_nil]
  dsimp [carryLengthBound]
  omega

theorem quotient_remainder_succ_no_carry {m n : ℕ} (hm : 2 ≤ m) (hr : n%m+1 < m) :
    (n+1)/m = n/m ∧ (n+1)%m = n%m+1 := by
  have hnum : n+1 = m*(n/m)+(n%m+1) := by
    have := Nat.mod_add_div n m
    omega
  rw [hnum, Nat.mul_add_div (by omega), Nat.mul_add_mod,
    Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]
  simp

theorem quotient_remainder_succ_carry {m n : ℕ} (hm : 2 ≤ m) (hr : n%m+1 = m) :
    n+1 = m*(n/m+1) ∧ (n+1)/m = n/m+1 ∧ (n+1)%m = 0 := by
  have hnum : n+1 = m*(n/m+1) := by
    rw [Nat.mul_add, Nat.mul_one]
    have := Nat.mod_add_div n m
    omega
  refine ⟨hnum, ?_, ?_⟩
  · rw [hnum, Nat.mul_div_cancel_left _ (show 0 < m by omega)]
  · rw [hnum, Nat.mul_mod_right]





end AbelianTargets


