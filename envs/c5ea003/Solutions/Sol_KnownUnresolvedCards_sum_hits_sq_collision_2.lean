-- Prove2me | solution 2 for KnownUnresolvedCards.sum_hits_sq_collision
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:01:32.771728+00:00
-- url     : https://prove2.me/submissions/05cbb3e2-3b67-481e-9939-32dd8b1972b9

import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_PermCount

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/MachineLearning/KnownUnresolvedCards/PermCount.lean ====
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Known versus unresolved cards — II. Fibre counting for shuffled decks

The unresolved part of a deck is modelled by a uniformly random bijection
`σ : α ≃ α` between *slots* and *cards*.  A *strategy* is an arbitrary function
`g : α → α` ("in slot `i` I predict card `g i`"); it need not be injective, so a
gambler is allowed to name the same card twice.

Everything about the mean and variance of the score of such a strategy is
controlled by two combinatorial counts:

* `fiber i a`  — permutations with `σ i = a`;
* `fiber₂ i j a b` — permutations with `σ i = a` and `σ j = b`.

We compute both **without ever mentioning a factorial**, using only the
transitivity of the left translation action of transpositions on
`Equiv.Perm α`:

* `card_fiber_mul`  : `|α| * |fiber i a| = |Perm α|`;
* `card_fiber₂_mul` : `(|α| - 1) * |fiber₂ i j a b| = |fiber i a|` for `i ≠ j`, `a ≠ b`.

## Main results

* `card_fiber_eq`, `card_fiber₂_eq` — transposition symmetry of the fibres.
* `card_fiber_mul`, `card_fiber₂_mul` — the two counting identities.
* `sum_hits_eq_card_perm` — **strategy invariance of the mean**: for *every*
  `g : α → α`, `∑ σ, hits g σ = |Perm α|`, i.e. the mean score is exactly `1`.
* `sum_hits_sq_eq_two_mul` — for an *injective* strategy the second moment is
  `2 |Perm α|`.
* `sum_hits_sq_collision` — the second moment of an **arbitrary** strategy,
  governed by its collision profile `distinctCallPairs`.
* `hits_const_eq_one` — a constant strategy scores exactly `1`, deterministically.
-/

namespace KnownUnresolvedCards

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## The two fibres -/

-- [dropped: platform already declares fiber]
-- [dropped: platform already declares fiber₂]
@[simp] lemma mem_fiber {i a : α} {σ : Equiv.Perm α} : σ ∈ fiber i a ↔ σ i = a := by
  simp [fiber]

@[simp] lemma mem_fiber₂ {i j a b : α} {σ : Equiv.Perm α} :
    σ ∈ fiber₂ i j a b ↔ σ i = a ∧ σ j = b := by
  simp [fiber₂]

lemma fiber₂_diag (i a : α) : fiber₂ i i a a = fiber i a := by
  ext σ; simp

/-- Two slots cannot both receive the same card. -/
lemma fiber₂_eq_empty_of_ne {i j : α} (hij : i ≠ j) (a : α) : fiber₂ i j a a = ∅ := by
  ext σ
  simp only [mem_fiber₂, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2
  exact hij (σ.injective (h1.trans h2.symm))

/-! ## Transposition symmetry -/

/-- Left translation by the transposition `(a b)` identifies the fibre over `a`
with the fibre over `b`: the card occupying a fixed slot is uniform. -/
lemma card_fiber_eq (i a b : α) : (fiber i a).card = (fiber i b).card := by
  refine Finset.card_nbij' (fun σ => Equiv.swap a b * σ) (fun σ => Equiv.swap a b * σ)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    have h : σ i = a := by simpa using hσ
    simp [Equiv.Perm.mul_apply, h]
  · intro σ hσ
    have h : σ i = b := by simpa using hσ
    simp [Equiv.Perm.mul_apply, h]
  · intro σ _
    simp [← mul_assoc, Equiv.swap_mul_self]
  · intro σ _
    simp [← mul_assoc, Equiv.swap_mul_self]

/-- Left translation by `(b b')`, which fixes `a`, identifies the two-slot
fibres `(a, b)` and `(a, b')`. -/
lemma card_fiber₂_eq (i j a b b' : α) (hb : a ≠ b) (hb' : a ≠ b') :
    (fiber₂ i j a b).card = (fiber₂ i j a b').card := by
  refine Finset.card_nbij' (fun σ => Equiv.swap b b' * σ) (fun σ => Equiv.swap b b' * σ)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    have h : σ i = a ∧ σ j = b := by simpa using hσ
    refine Finset.mem_coe.mpr (mem_fiber₂.mpr ⟨?_, ?_⟩)
    · simp [Equiv.Perm.mul_apply, h.1, Equiv.swap_apply_of_ne_of_ne hb hb']
    · simp [Equiv.Perm.mul_apply, h.2]
  · intro σ hσ
    have h : σ i = a ∧ σ j = b' := by simpa using hσ
    refine Finset.mem_coe.mpr (mem_fiber₂.mpr ⟨?_, ?_⟩)
    · simp [Equiv.Perm.mul_apply, h.1, Equiv.swap_apply_of_ne_of_ne hb hb']
    · simp [Equiv.Perm.mul_apply, h.2]
  · intro σ _
    simp [← mul_assoc, Equiv.swap_mul_self]
  · intro σ _
    simp [← mul_assoc, Equiv.swap_mul_self]

/-! ## The counting identities -/

lemma sum_card_fiber (i : α) : ∑ a, (fiber i a).card = Fintype.card (Equiv.Perm α) := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm α => σ i) (s := (univ : Finset (Equiv.Perm α)))
    (t := (univ : Finset α)) (fun σ _ => mem_univ _)
  rw [Finset.card_univ] at h
  rw [h]
  exact Finset.sum_congr rfl fun a _ => by rw [fiber]

/-- **First counting identity.**  Exactly a `1/|α|` fraction of all permutations
puts a prescribed card in a prescribed slot. -/
theorem card_fiber_mul (i a : α) :
    Fintype.card α * (fiber i a).card = Fintype.card (Equiv.Perm α) := by
  rw [← sum_card_fiber i]
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ (univ : Finset α)) => card_fiber_eq i b a)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

lemma sum_card_fiber₂ (i j : α) (a : α) :
    ∑ b, (fiber₂ i j a b).card = (fiber i a).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm α => σ j) (s := fiber i a)
    (t := (univ : Finset α)) (fun σ _ => mem_univ _)
  rw [h]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ext σ
  simp

/-- **Second counting identity.**  Given that slot `i` holds card `a`, the card
in a different slot `j` is uniform over the remaining `|α| - 1` cards. -/
theorem card_fiber₂_mul {i j a b : α} (hij : i ≠ j) (hab : a ≠ b) :
    (Fintype.card α - 1) * (fiber₂ i j a b).card = (fiber i a).card := by
  classical
  rw [← sum_card_fiber₂ i j a]
  rw [← Finset.sum_erase_add (univ : Finset α) _ (mem_univ a)]
  rw [fiber₂_eq_empty_of_ne hij a]
  simp only [Finset.card_empty, add_zero]
  rw [Finset.sum_congr rfl
    (fun b' (hb' : b' ∈ (univ : Finset α).erase a) =>
      card_fiber₂_eq i j a b' b (Ne.symm (Finset.mem_erase.mp hb').1) hab)]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (mem_univ a), Finset.card_univ]

/-! ## The score of a strategy -/

-- [dropped: platform already declares hits]
lemma hits_eq_sum (g : α → α) (σ : Equiv.Perm α) :
    hits g σ = ∑ i, (if σ i = g i then 1 else 0) := by
  rw [hits, Finset.card_filter]

lemma sum_hits (g : α → α) :
    ∑ σ : Equiv.Perm α, hits g σ = ∑ i, (fiber i (g i)).card := by
  simp only [hits_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fiber, Finset.card_filter]

/-- **Strategy invariance of the mean score.**  For *every* strategy `g`
— injective or not, clever or not — the total number of correct calls summed
over all shuffles equals `|Perm α|`; the mean score is exactly `1`.
Uncertainty offers no edge, and no strategy is better than any other. -/
theorem sum_hits_eq_card_perm [Nonempty α] (g : α → α) :
    ∑ σ : Equiv.Perm α, hits g σ = Fintype.card (Equiv.Perm α) := by
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [sum_hits, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (univ : Finset α)) => card_fiber_mul i (g i))]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Expansion of the second moment as a double sum of two-slot fibre counts. -/
lemma sum_hits_sq_eq_sum_fiber₂ (g : α → α) :
    ∑ σ : Equiv.Perm α, (hits g σ) ^ 2 = ∑ i, ∑ j, (fiber₂ i j (g i) (g j)).card := by
  have hexp : ∀ σ : Equiv.Perm α,
      (hits g σ) ^ 2 = ∑ i, ∑ j, (if σ i = g i ∧ σ j = g j then 1 else 0) := by
    intro σ
    rw [hits_eq_sum, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : σ i = g i <;> by_cases h2 : σ j = g j <;> simp [h1, h2]
  simp only [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fiber₂, Finset.card_filter]

/-- Second moment of the score of an injective strategy. -/
theorem sum_hits_sq_eq_two_mul (hcard : 2 ≤ Fintype.card α)
    {g : α → α} (hg : Function.Injective g) :
    ∑ σ : Equiv.Perm α, (hits g σ) ^ 2 = 2 * Fintype.card (Equiv.Perm α) := by
  classical
  have hpos : 0 < Fintype.card α := lt_of_lt_of_le (by norm_num) hcard
  have hpos' : 0 < Fintype.card α - 1 := by omega
  have hswap := sum_hits_sq_eq_sum_fiber₂ g
  -- The inner sum is twice the one-slot fibre count.
  have hinner : ∀ i : α, ∑ j, (fiber₂ i j (g i) (g j)).card = 2 * (fiber i (g i)).card := by
    intro i
    rw [← Finset.sum_erase_add (univ : Finset α) _ (mem_univ i)]
    rw [fiber₂_diag]
    have hoff : ∑ j ∈ (univ : Finset α).erase i, (fiber₂ i j (g i) (g j)).card
        = (fiber i (g i)).card := by
      refine Nat.eq_of_mul_eq_mul_left hpos' ?_
      rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun j (hj : j ∈ (univ : Finset α).erase i) =>
        card_fiber₂_mul (Ne.symm (Finset.mem_erase.mp hj).1)
          (fun h => (Finset.mem_erase.mp hj).1 (hg h.symm)))]
      rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (mem_univ i),
        Finset.card_univ]
    rw [hoff]
    ring
  rw [hswap]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (univ : Finset α)) => hinner i)]
  rw [← Finset.mul_sum]
  congr 1
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (univ : Finset α)) => card_fiber_mul i (g i))]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ## The collision profile of a strategy -/

-- [dropped: platform already declares distinctCalls]
-- [dropped: platform already declares distinctCallPairs]
lemma distinctCallPairs_eq_card (g : α → α) :
    distinctCallPairs g
      = ((univ : Finset (α × α)).filter (fun p => g p.1 ≠ g p.2)).card := by
  rw [distinctCallPairs, Finset.card_filter, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => by rw [distinctCalls, Finset.card_filter]

lemma distinctCalls_of_injective {g : α → α} (hg : Function.Injective g) (i : α) :
    distinctCalls g i = Fintype.card α - 1 := by
  have : (univ.filter (fun j => g i ≠ g j)) = (univ : Finset α).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, mem_univ, and_true, true_and]
    constructor
    · intro h hji; exact h (by rw [hji])
    · intro h hgij; exact h (hg hgij).symm
  rw [distinctCalls, this, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ]

lemma distinctCallPairs_of_injective {g : α → α} (hg : Function.Injective g) :
    distinctCallPairs g = Fintype.card α * (Fintype.card α - 1) := by
  rw [distinctCallPairs,
    Finset.sum_congr rfl (fun i (_ : i ∈ (univ : Finset α)) => distinctCalls_of_injective hg i),
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

@[simp] lemma distinctCallPairs_const (a : α) : distinctCallPairs (fun _ : α => a) = 0 := by
  simp [distinctCallPairs, distinctCalls]

/-- One row of the second-moment expansion: the diagonal term contributes the
one-slot count, and each slot calling a *different* card contributes the same
count again after division by `u - 1`. -/
lemma sum_fiber₂_row (g : α → α) (i : α) :
    (Fintype.card α - 1) * ∑ j, (fiber₂ i j (g i) (g j)).card
      = ((Fintype.card α - 1) + distinctCalls g i) * (fiber i (g i)).card := by
  classical
  rw [← Finset.sum_erase_add (univ : Finset α) _ (mem_univ i), fiber₂_diag, Nat.mul_add]
  have hoff : (Fintype.card α - 1) * ∑ j ∈ (univ : Finset α).erase i,
      (fiber₂ i j (g i) (g j)).card = distinctCalls g i * (fiber i (g i)).card := by
    rw [Finset.mul_sum]
    have hterm : ∀ j ∈ (univ : Finset α).erase i,
        (Fintype.card α - 1) * (fiber₂ i j (g i) (g j)).card
          = if g i ≠ g j then (fiber i (g i)).card else 0 := by
      intro j hj
      have hij : i ≠ j := (Ne.symm (Finset.mem_erase.mp hj).1)
      by_cases hgc : g i = g j
      · rw [if_neg (by simpa using hgc), hgc, fiber₂_eq_empty_of_ne hij (g j)]
        simp
      · rw [if_pos hgc, card_fiber₂_mul hij hgc]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      add_zero, smul_eq_mul]
    congr 1
    rw [distinctCalls]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, mem_univ, and_true, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨fun hji => h (by rw [hji]), h⟩
  rw [hoff]
  ring

/-- **The collision formula for the second moment.**  For an arbitrary strategy
`g` — injective or not — the second moment of the blind score is governed by the
collision profile of `g` alone.  Together with `sum_hits_eq_card_perm` (the mean
is always `1`) this exhibits the exact boundary of strategy invariance: the first
moment cannot see the strategy, the second moment sees precisely its pattern of
repeated calls. -/
theorem sum_hits_sq_collision (g : α → α) :
    Fintype.card α * (Fintype.card α - 1) * (∑ σ : Equiv.Perm α, (hits g σ) ^ 2)
      = (Fintype.card α * (Fintype.card α - 1) + distinctCallPairs g)
          * Fintype.card (Equiv.Perm α) := by
  classical
  rw [sum_hits_sq_eq_sum_fiber₂ g, Finset.mul_sum]
  have hrow : ∀ i : α,
      Fintype.card α * (Fintype.card α - 1) * (∑ j, (fiber₂ i j (g i) (g j)).card)
        = ((Fintype.card α - 1) + distinctCalls g i) * Fintype.card (Equiv.Perm α) := by
    intro i
    calc Fintype.card α * (Fintype.card α - 1) * (∑ j, (fiber₂ i j (g i) (g j)).card)
        = Fintype.card α * ((Fintype.card α - 1) * ∑ j, (fiber₂ i j (g i) (g j)).card) := by
          ring
      _ = Fintype.card α * (((Fintype.card α - 1) + distinctCalls g i) * (fiber i (g i)).card) := by
          rw [sum_fiber₂_row g i]
      _ = ((Fintype.card α - 1) + distinctCalls g i) * (Fintype.card α * (fiber i (g i)).card) := by
          ring
      _ = ((Fintype.card α - 1) + distinctCalls g i) * Fintype.card (Equiv.Perm α) := by
          rw [card_fiber_mul i (g i)]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (univ : Finset α)) => hrow i)]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    distinctCallPairs]

/-- A *constant* strategy — naming the same card in every slot — scores exactly
one, with no randomness at all. -/
theorem hits_const_eq_one [Nonempty α] (a : α) (σ : Equiv.Perm α) :
    hits (fun _ => a) σ = 1 := by
  have : (univ.filter (fun i => σ i = a)) = {σ.symm a} := by
    ext i
    simp [Equiv.eq_symm_apply]
  rw [hits, this, Finset.card_singleton]

/-- Second moment of a constant strategy: `|Perm α|`, i.e. `E[hits²] = 1`. -/
theorem sum_hits_sq_const [Nonempty α] (a : α) :
    ∑ σ : Equiv.Perm α, (hits (fun _ => a) σ) ^ 2 = Fintype.card (Equiv.Perm α) := by
  rw [Finset.sum_congr rfl (fun σ (_ : σ ∈ (univ : Finset (Equiv.Perm α))) => by
    rw [hits_const_eq_one a σ])]
  simp [Finset.card_univ]

end KnownUnresolvedCards
section
open KnownUnresolvedCards
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem solution (g : α → α) :
    Fintype.card α * (Fintype.card α - 1) * (∑ σ : Equiv.Perm α, (hits g σ) ^ 2)
      = (Fintype.card α * (Fintype.card α - 1) + distinctCallPairs g)
          * Fintype.card (Equiv.Perm α) :=
  KnownUnresolvedCards.sum_hits_sq_collision g

end
