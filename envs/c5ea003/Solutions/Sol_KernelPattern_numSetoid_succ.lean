-- Prove2me | solution 1 for KernelPattern.numSetoid_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:03:27.555688+00:00
-- url     : https://prove2.me/submissions/7663377b-ad9e-49c9-a736-5dfe571f5763

-- Sol generated from Algebra/KernelPatterns/SetoidCount.lean
import Mathlib
import Definitions.Def_Algebra_KernelPatterns_SetoidCount
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



theorem natCard_setoid_congr (e : α ≃ β) : Nat.card (Setoid α) = Nat.card (Setoid β) :=
  Nat.card_congr (setoidCongr e)


theorem natCard_setoid_eq_numSetoid (α : Type*) [Fintype α] :
    Nat.card (Setoid α) = numSetoid (Fintype.card α) :=
  natCard_setoid_congr (Fintype.equivFin α)

/-! ## The block of the distinguished point -/

variable [Fintype β]



variable [DecidableEq β]


variable {S : Finset β} {t : Setoid {b : β // b ∉ S}} {a b c : β}















/-! ## The recurrence -/

theorem natCard_setoid_option :
    Nat.card (Setoid (Option β)) = ∑ S : Finset β, Nat.card (Setoid {b : β // b ∉ S}) := by
  classical
  have h1 : Nat.card (Setoid (Option β))
      = Nat.card (Σ S : Finset β, {s : Setoid (Option β) // blockOfNone s = S}) :=
    (Nat.card_congr (Equiv.sigmaFiberEquiv blockOfNone)).symm
  rw [h1, Nat.card_sigma]
  exact Finset.sum_congr rfl fun S _ => Nat.card_congr (fiberEquiv S)

theorem natCard_setoid_compl (S : Finset β) :
    Nat.card (Setoid {b : β // b ∉ S}) = numSetoid (Fintype.card β - S.card) := by
  classical
  rw [natCard_setoid_eq_numSetoid]
  congr 1
  have h1 : Fintype.card {b : β // b ∈ S} = S.card := Fintype.card_coe S
  rw [Fintype.card_subtype_compl, h1]





open KernelPattern in
theorem solution(n : ℕ) :
    numSetoid (n + 1) = ∑ k ∈ range (n + 1), n.choose k * numSetoid (n - k) := by
  classical
  have h0 : numSetoid (n + 1) = Nat.card (Setoid (Option (Fin n))) :=
    natCard_setoid_congr (finSuccEquiv n)
  rw [h0, natCard_setoid_option]
  have hterm : ∀ S : Finset (Fin n), Nat.card (Setoid {b : Fin n // b ∉ S})
      = numSetoid (n - S.card) := by
    intro S
    rw [natCard_setoid_compl]
    simp
  rw [Finset.sum_congr rfl fun S (_ : S ∈ (univ : Finset (Finset (Fin n)))) => hterm S]
  have hpow : ∑ S ∈ (univ : Finset (Fin n)).powerset, numSetoid (n - S.card)
      = ∑ j ∈ range ((univ : Finset (Fin n)).card + 1),
          ∑ S ∈ Finset.powersetCard j (univ : Finset (Fin n)), numSetoid (n - S.card) :=
    Finset.sum_powerset _ _
  rw [Finset.powerset_univ] at hpow
  rw [hpow, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : ∀ S ∈ Finset.powersetCard j (univ : Finset (Fin n)),
      numSetoid (n - S.card) = numSetoid (n - j) := by
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
