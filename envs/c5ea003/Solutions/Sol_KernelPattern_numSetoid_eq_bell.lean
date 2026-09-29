-- Prove2me | solution 1 for KernelPattern.numSetoid_eq_bell
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:04:50.068792+00:00
-- url     : https://prove2.me/submissions/d8b3bbe8-1661-44d0-9937-16ef95361fca

-- Sol generated from Algebra/KernelPatterns/SetoidCount.lean
import Mathlib
import Definitions.Def_Algebra_KernelPatterns_SetoidCount
import Theorems.Thm_KernelPattern_numSetoid_succ
/-
# Counting equivalence relations: the Bell numbers

Mathlib defines `Nat.bell` by the binomial recurrence
`bell (n+1) = ∑ i : Fin (n+1), (n.choose i) * bell (n - i)` and records as a TODO
that it counts the partitions of an `n`-element set.  This file proves exactly
that statement in the form

`KernelPattern.numSetoid n = Nat.bell n`,  where  `numSetoid n = Nat.card (Setoid (Fin n))`

is the number of equivalence relations on `Fin n`.

The proof is the classical "block of the distinguished point" decomposition, carried
out over `Option β`: an equivalence relation on `Option β` is the same data as a
subset `S ⊆ β` (the partners of the extra point `none`) together with an arbitrary
equivalence relation on the complement of `S`.  This is formalised as a fibration
`blockOfNone : Setoid (Option β) → Finset β` whose fibre over `S` is canonically
equivalent to `Setoid {b // b ∉ S}`.
-/

open KernelPattern

open Finset

variable {α β : Type*}

/-! ## Finiteness and transport -/






/-! ## The block of the distinguished point -/

variable [Fintype β]



variable [DecidableEq β]


variable {S : Finset β} {t : Setoid {b : β // b ∉ S}} {a b c : β}















/-! ## The recurrence -/




theorem numSetoid_zero : numSetoid 0 = 1 := by
  have hsub : Subsingleton (Setoid (Fin 0)) := ⟨fun s t => Setoid.ext fun a => a.elim0⟩
  have hne : Nonempty (Setoid (Fin 0)) := ⟨⊥⟩
  rw [numSetoid, Nat.card_eq_one_iff_unique]
  exact ⟨hsub, hne⟩



open KernelPattern in
theorem solution(n : ℕ) : numSetoid n = Nat.bell n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simpa using numSetoid_zero
    | (m + 1), ih =>
      rw [numSetoid_succ, Nat.bell_succ,
        Fin.sum_univ_eq_sum_range (fun k => m.choose k * Nat.bell (m - k)) (m + 1)]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hlt : m - k < m + 1 := by omega
      rw [ih _ hlt]
