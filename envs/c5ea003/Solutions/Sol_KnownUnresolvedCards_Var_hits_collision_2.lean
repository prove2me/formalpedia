-- Prove2me | solution 2 for KnownUnresolvedCards.Var_hits_collision
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:00:54.207227+00:00
-- url     : https://prove2.me/submissions/89a94fed-452e-4c8e-be53-1d6b7347a0b0

import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_DeckGame
import Definitions.Def_MachineLearning_KnownUnresolvedCards_PermCount

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/MachineLearning/KnownUnresolvedCards/Basic.lean ====
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Known versus unresolved cards — I. The uniform expectation calculus

A *prediction game* pays a rational amount on each of finitely many **cards**.
Some cards are **resolved**: the predictor knows their value and collects a
deterministic unit payoff.  The remaining cards are **unresolved**: the predictor
must guess, and the guess is priced at *fair odds*, i.e. the payoff on such a
card has zero mean.

This file develops the minimal probabilistic infrastructure needed to state and
prove the headline principle

> `E[total payoff] = (number of resolved cards)`,

namely a uniform-expectation functional `E` on a finite sample space, its
linearity, and the **splitting theorem** `expected_total_eq_certain_count`.

The point of stating the splitting theorem for an *arbitrary* finite index type
`ι` and an *arbitrary* subset `K : Finset ι` of resolved cards is that the deck
models of `PermCount.lean` and `DeckGame.lean` are then genuine instances rather
than re-proofs.

## Main results

* `E_sum` — linearity of uniform expectation over a `Finset` sum.
* `expected_total_eq_certain_count` — if every card of `K` pays a deterministic
  `1` and every card outside `K` is fair, the expected total payoff is `K.card`.
* `expected_total_eq_certain_sum` — the weighted version with arbitrary
  deterministic payoffs on `K`.
* `no_fair_portfolio_edge` — a portfolio consisting only of fair cards has zero
  expected payoff, *whatever* the (possibly wildly correlated) joint law.
-/

namespace KnownUnresolvedCards

open Finset

/-! ## Uniform expectation on a finite sample space -/

variable {Ω : Type*} [Fintype Ω]

-- [dropped: platform already declares E]
lemma E_def (f : Ω → ℚ) : E f = (∑ ω, f ω) / (Fintype.card Ω : ℚ) := rfl

lemma card_ne_zero [Nonempty Ω] : ((Fintype.card Ω : ℚ)) ≠ 0 := by
  have : 0 < Fintype.card Ω := Fintype.card_pos
  positivity

@[simp] lemma E_const [Nonempty Ω] (c : ℚ) : E (fun _ : Ω => c) = c := by
  have h := card_ne_zero (Ω := Ω)
  rw [E_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma E_add (f g : Ω → ℚ) : E (fun ω => f ω + g ω) = E f + E g := by
  simp only [E_def, Finset.sum_add_distrib]
  ring

lemma E_smul (c : ℚ) (f : Ω → ℚ) : E (fun ω => c * f ω) = c * E f := by
  simp only [E_def, ← Finset.mul_sum]
  ring

lemma E_neg (f : Ω → ℚ) : E (fun ω => -f ω) = -E f := by
  simp only [E_def, Finset.sum_neg_distrib]
  ring

/-- Linearity of the uniform expectation over a finite family of observables. -/
lemma E_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℚ) :
    E (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, E (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [E_def]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [E_add, ih]

-- [dropped: platform already declares Var]
lemma Var_def (f : Ω → ℚ) : Var f = E (fun ω => f ω ^ 2) - (E f) ^ 2 := rfl

/-! ## Resolved and unresolved cards -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- [dropped: platform already declares Resolved]
-- [dropped: platform already declares Fair]
lemma E_of_resolved [Nonempty Ω] {p : Ω → ℚ} {c : ℚ} (h : Resolved p c) : E p = c := by
  have hp : (fun ω : Ω => p ω) = (fun _ : Ω => c) := funext h
  simp [show p = (fun _ : Ω => c) from hp]

/-- **Splitting theorem, weighted form.**  If the cards indexed by `K` are
resolved with values `c i` and every card outside `K` is fair, then the expected
total payoff is `∑ i ∈ K, c i`: the unresolved cards contribute nothing. -/
theorem expected_total_eq_certain_sum [Nonempty Ω]
    (p : ι → Ω → ℚ) (K : Finset ι) (c : ι → ℚ)
    (hK : ∀ i ∈ K, Resolved (p i) (c i))
    (hU : ∀ i ∉ K, Fair (p i)) :
    E (fun ω => ∑ i, p i ω) = ∑ i ∈ K, c i := by
  classical
  rw [E_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ K)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => i ∈ K), E (p i) = ∑ i ∈ K, c i := by
    have : Finset.univ.filter (fun i => i ∈ K) = K := by
      ext i; simp
    rw [this]
    exact Finset.sum_congr rfl fun i hi => E_of_resolved (hK i hi)
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => i ∉ K), E (p i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hU i (by simpa using (Finset.mem_filter.mp hi).2)
  rw [h1, h2, add_zero]

/-- **Splitting theorem (headline form).**  `d` cards predicted with certainty
each pay one unit, the remaining cards are fair guesses; the expected payoff is
exactly `d = K.card`.  Uncertainty supplies no positive edge. -/
theorem expected_total_eq_certain_count [Nonempty Ω]
    (p : ι → Ω → ℚ) (K : Finset ι)
    (hK : ∀ i ∈ K, Resolved (p i) 1)
    (hU : ∀ i ∉ K, Fair (p i)) :
    E (fun ω => ∑ i, p i ω) = (K.card : ℚ) := by
  have := expected_total_eq_certain_sum (Ω := Ω) p K (fun _ => 1) hK hU
  simpa using this

/-- **No edge from uncertainty alone.**  A portfolio built exclusively out of
fair cards has zero expected payoff — regardless of how the cards are
correlated, and regardless of how cleverly the guesses were chosen. -/
theorem no_fair_portfolio_edge [Nonempty Ω]
    (p : ι → Ω → ℚ) (hU : ∀ i, Fair (p i)) :
    E (fun ω => ∑ i, p i ω) = 0 := by
  have := expected_total_eq_certain_count (Ω := Ω) p ∅ (by simp) (by simpa using hU)
  simpa using this

end KnownUnresolvedCards
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
-- ==== upstream: Packages/Catalog/MachineLearning/KnownUnresolvedCards/DeckGame.lean ====
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Known versus unresolved cards — III. The deck game

We now assemble the pieces.  A deck consists of

* `d` **resolved** cards, each paying a deterministic unit;
* an **unresolved** block indexed by a nonempty finite type `α`, whose true
  arrangement is a uniformly random bijection `σ : α ≃ α` and on which the
  predictor plays an arbitrary strategy `g : α → α`.

The scoring of an unresolved slot is `w` on a hit and `l` on a miss.

## Main results

* `E_slotScore` — the **master formula** for a single unresolved slot:
  `E = (w - l)/|α| + l`, *independent of the slot and of the strategy*.
* `expected_deckScore` — for the whole unresolved block,
  `E = (w - l) + l * |α|`.
* `fair_odds_iff` — **rigidity of fair odds**: the unresolved block has zero
  expected value iff `w = l * (1 - |α|)`; for `l = -1` this is exactly the
  `(|α| - 1) : 1` payout.  So the "no edge" phenomenon is not an accident of a
  lucky normalisation: it *characterises* fair odds.
* `expected_gamePayoff_eq_known` — **the headline theorem**: with `d` resolved
  cards and a fair-odds unresolved block, the expected payoff is exactly `d`.
* `expected_unit_score_eq_known_add_one` — **the counting anomaly**: with naive
  unit scoring (`1` for a hit, `0` for a miss) the expected payoff is `d + 1`,
  for *every* strategy and *every* size of the unresolved block.  The apparent
  "edge" of uncertainty is one single card, and it is a scoring artefact.
* `Var_hits_collision` — the exact variance of an arbitrary strategy, equal to
  its normalised collision profile.
* `Var_hits_injective`, `Var_hits_const` — **second-moment dichotomy**: the mean score
  is strategy-invariant but the variance is not (`1` for an injective strategy,
  `0` for a constant one).  Uncertainty offers no edge in the mean, yet the
  strategy fully controls the risk.
-/


namespace KnownUnresolvedCards

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## A single unresolved slot -/

-- [dropped: platform already declares slotScore]
lemma sum_slotScore (w l : ℚ) (i a : α) :
    ∑ σ : Equiv.Perm α, slotScore w l i a σ
      = (w - l) * ((fiber i a).card : ℚ) + l * (Fintype.card (Equiv.Perm α) : ℚ) := by
  have h1 : ∀ σ : Equiv.Perm α,
      slotScore w l i a σ = (w - l) * (if σ i = a then (1 : ℚ) else 0) + l := by
    intro σ
    by_cases h : σ i = a <;> simp [slotScore, h]
  rw [Finset.sum_congr rfl (fun σ (_ : σ ∈ (univ : Finset (Equiv.Perm α))) => h1 σ)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [fiber]
  ring

/-- **Master formula for one unresolved slot.**  Whatever card is named, the
expected score of a single slot of an unresolved block of size `|α|` is
`(w - l)/|α| + l`. -/
theorem E_slotScore [Nonempty α] (w l : ℚ) (i a : α) :
    E (slotScore w l i a) = (w - l) / (Fintype.card α : ℚ) + l := by
  have hu : 0 < Fintype.card α := Fintype.card_pos
  have hP : 0 < Fintype.card (Equiv.Perm α) := Fintype.card_pos
  have hkey : Fintype.card α * (fiber i a).card = Fintype.card (Equiv.Perm α) :=
    card_fiber_mul i a
  have hN : 0 < (fiber i a).card := by
    rcases Nat.eq_zero_or_pos (fiber i a).card with h | h
    · rw [h, Nat.mul_zero] at hkey; omega
    · exact h
  have hkeyQ : (Fintype.card α : ℚ) * ((fiber i a).card : ℚ)
      = (Fintype.card (Equiv.Perm α) : ℚ) := by exact_mod_cast hkey
  have huQ : ((Fintype.card α : ℚ)) ≠ 0 := by positivity
  have hNQ : (((fiber i a).card : ℚ)) ≠ 0 := by positivity
  rw [E_def, sum_slotScore, ← hkeyQ]
  field_simp

/-! ## The whole unresolved block -/

-- [dropped: platform already declares deckScore]
/-- **The unresolved block has expected value `(w - l) + l * |α|`** — for every
strategy `g`, injective or not. -/
theorem expected_deckScore [Nonempty α] (w l : ℚ) (g : α → α) :
    E (deckScore w l g) = (w - l) + l * (Fintype.card α : ℚ) := by
  have hu : ((Fintype.card α : ℚ)) ≠ 0 := by
    have : 0 < Fintype.card α := Fintype.card_pos
    positivity
  have : E (fun σ : Equiv.Perm α => ∑ i, slotScore w l i (g i) σ)
      = ∑ _i : α, ((w - l) / (Fintype.card α : ℚ) + l) := by
    rw [E_sum]
    exact Finset.sum_congr rfl fun i _ => E_slotScore w l i (g i)
  have hd : deckScore w l g = fun σ : Equiv.Perm α => ∑ i, slotScore w l i (g i) σ := rfl
  rw [hd, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Rigidity of fair odds.**  The unresolved block is a zero-expectation bet
precisely when the payout ratio is the fair one; no other normalisation of the
scoring makes uncertainty edge-free. -/
theorem fair_odds_iff [Nonempty α] (w l : ℚ) (g : α → α) :
    E (deckScore w l g) = 0 ↔ w = l * (1 - (Fintype.card α : ℚ)) := by
  rw [expected_deckScore]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- Fair odds on an unresolved block of size `u`: `u - 1` for a hit, `-1` for a
miss.  Its expected value is zero. -/
theorem expected_fairOdds [Nonempty α] (g : α → α) :
    E (deckScore ((Fintype.card α : ℚ) - 1) (-1) g) = 0 := by
  rw [fair_odds_iff]; ring

/-- Naive unit scoring: `1` for a hit, `0` for a miss.  The expected number of
correct calls on the unresolved block is exactly `1`, whatever the strategy and
however large the block. -/
theorem expected_unit_score [Nonempty α] (g : α → α) :
    E (deckScore 1 0 g) = 1 := by
  rw [expected_deckScore]; ring

/-! ## The full game: resolved cards plus an unresolved block -/

-- [dropped: platform already declares gamePayoff]
/-- **Headline theorem: known versus unresolved cards.**  If `d` cards are
predicted with certainty and the remaining `u = |α|` cards are fair guesses,
the expected payoff is exactly `d`.  Uncertainty supplies no positive edge. -/
theorem expected_gamePayoff_eq_known [Nonempty α] (d : ℕ) (g : α → α) :
    E (fun σ : Equiv.Perm α => ∑ c : Fin d ⊕ α, gamePayoff d g c σ) = (d : ℚ) := by
  classical
  set K : Finset (Fin d ⊕ α) := (univ : Finset (Fin d)).map ⟨Sum.inl, Sum.inl_injective⟩ with hK
  have hcard : K.card = d := by simp [hK]
  have hres : ∀ c ∈ K, Resolved (gamePayoff d g c) 1 := by
    intro c hc
    rw [hK, Finset.mem_map] at hc
    obtain ⟨a, -, rfl⟩ := hc
    intro σ; rfl
  have hfair : ∀ c ∉ K, Fair (gamePayoff d g c) := by
    intro c hc
    rcases c with a | b
    · exact absurd (by simp [hK]) hc
    · have := E_slotScore (α := α) ((Fintype.card α : ℚ) - 1) (-1) b (g b)
      have hu : ((Fintype.card α : ℚ)) ≠ 0 := by
        have : 0 < Fintype.card α := Fintype.card_pos
        positivity
      rw [Fair, show gamePayoff d g (Sum.inr b)
          = slotScore ((Fintype.card α : ℚ) - 1) (-1) b (g b) from rfl, this]
      field_simp
      ring
  have := expected_total_eq_certain_count (Ω := Equiv.Perm α) (gamePayoff d g) K hres hfair
  rw [this, hcard]

/-- **The counting anomaly.**  Under naive unit scoring the expected number of
correct calls is `d + 1`, not `d`: the unresolved block contributes exactly one
extra hit, independently of its size and of the strategy.  This single card is
the whole of the apparent "edge" of uncertainty, and `fair_odds_iff` shows it is
purely an artefact of the scoring. -/
theorem expected_unit_score_eq_known_add_one [Nonempty α] (d : ℕ) (g : α → α) :
    E (fun σ : Equiv.Perm α => (d : ℚ) + deckScore 1 0 g σ) = (d : ℚ) + 1 := by
  have h := E_add (Ω := Equiv.Perm α) (fun _ => (d : ℚ)) (deckScore 1 0 g)
  rw [h, E_const, expected_unit_score]

/-! ## Second-moment dichotomy -/

lemma deckScore_one_zero_eq_hits (g : α → α) (σ : Equiv.Perm α) :
    deckScore 1 0 g σ = (hits g σ : ℚ) := by
  rw [deckScore, hits_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by by_cases h : σ i = g i <;> simp [slotScore, h]

lemma E_hits [Nonempty α] (g : α → α) : E (fun σ : Equiv.Perm α => (hits g σ : ℚ)) = 1 := by
  have : (fun σ : Equiv.Perm α => (hits g σ : ℚ)) = deckScore 1 0 g :=
    funext fun σ => (deckScore_one_zero_eq_hits g σ).symm
  rw [this, expected_unit_score]

/-- The variance of the score of an *injective* strategy is `1`. -/
theorem Var_hits_injective (hcard : 2 ≤ Fintype.card α) {g : α → α} (hg : Function.Injective g) :
    Var (fun σ : Equiv.Perm α => (hits g σ : ℚ)) = 1 := by
  have hcpos : 0 < Fintype.card α := by omega
  have hne : Nonempty α := Fintype.card_pos_iff.mp hcpos
  have hP : (0 : ℚ) < (Fintype.card (Equiv.Perm α) : ℚ) := by
    have : 0 < Fintype.card (Equiv.Perm α) := Fintype.card_pos
    exact_mod_cast this
  have hPne : ((Fintype.card (Equiv.Perm α) : ℚ)) ≠ 0 := ne_of_gt hP
  have hsq : ∑ σ : Equiv.Perm α, ((hits g σ : ℚ)) ^ 2
      = 2 * (Fintype.card (Equiv.Perm α) : ℚ) := by
    have h := sum_hits_sq_eq_two_mul hcard hg
    have h' : ((∑ σ : Equiv.Perm α, (hits g σ) ^ 2 : ℕ) : ℚ)
        = ((2 * Fintype.card (Equiv.Perm α) : ℕ) : ℚ) := by rw [h]
    push_cast at h'
    exact h'
  rw [Var_def, E_hits g, E_def, hsq, mul_div_assoc, div_self hPne]
  norm_num

/-- A constant strategy has variance `0`: its score is the deterministic `1`. -/
theorem Var_hits_const [Nonempty α] (a : α) :
    Var (fun σ : Equiv.Perm α => (hits (fun _ => a) σ : ℚ)) = 0 := by
  have h : ∀ σ : Equiv.Perm α, ((hits (fun _ => a) σ : ℚ)) = 1 := by
    intro σ; rw [hits_const_eq_one a σ]; norm_num
  rw [Var_def]
  simp only [h, one_pow]
  simp

/-- **The collision formula for the variance.**  For an arbitrary strategy the
variance of the blind score is the normalised collision profile
`(number of ordered slot pairs with distinct calls) / (u(u-1))`.  It interpolates
between `1` (injective calls) and `0` (a constant call) and is the first
quantity in the game that can see the strategy at all. -/
theorem Var_hits_collision (hcard : 2 ≤ Fintype.card α) (g : α → α) :
    Var (fun σ : Equiv.Perm α => (hits g σ : ℚ))
      = (distinctCallPairs g : ℚ)
          / ((Fintype.card α : ℚ) * ((Fintype.card α : ℚ) - 1)) := by
  have hcpos : 0 < Fintype.card α := by omega
  have hne : Nonempty α := Fintype.card_pos_iff.mp hcpos
  have hP : (0 : ℚ) < (Fintype.card (Equiv.Perm α) : ℚ) := by
    have : 0 < Fintype.card (Equiv.Perm α) := Fintype.card_pos
    exact_mod_cast this
  have hPne : ((Fintype.card (Equiv.Perm α) : ℚ)) ≠ 0 := ne_of_gt hP
  have hu : ((Fintype.card α : ℚ)) ≠ 0 := by positivity
  have hu1 : ((Fintype.card α : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ (Fintype.card α : ℚ) := by exact_mod_cast hcard
    intro h; linarith
  have hQ : (Fintype.card α : ℚ) * ((Fintype.card α : ℚ) - 1)
        * (∑ σ : Equiv.Perm α, ((hits g σ : ℚ)) ^ 2)
      = ((Fintype.card α : ℚ) * ((Fintype.card α : ℚ) - 1) + (distinctCallPairs g : ℚ))
          * (Fintype.card (Equiv.Perm α) : ℚ) := by
    have h := congrArg (fun n : ℕ => (n : ℚ)) (sum_hits_sq_collision (α := α) g)
    push_cast [Nat.cast_sub (show 1 ≤ Fintype.card α by omega)] at h
    exact h
  rw [Var_def, E_hits g, E_def]
  field_simp
  linear_combination hQ

/-- Consistency check: an injective strategy has collision profile `u(u-1)`, so
variance `1`. -/
example (hcard : 2 ≤ Fintype.card α) {g : α → α} (hg : Function.Injective g) :
    Var (fun σ : Equiv.Perm α => (hits g σ : ℚ)) = 1 := by
  have hu : ((Fintype.card α : ℚ)) ≠ 0 := by
    have : 0 < Fintype.card α := by omega
    positivity
  have hu1 : ((Fintype.card α : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ (Fintype.card α : ℚ) := by exact_mod_cast hcard
    intro h; linarith
  rw [Var_hits_collision hcard g, distinctCallPairs_of_injective hg]
  push_cast [Nat.cast_sub (show 1 ≤ Fintype.card α by omega)]
  field_simp

/-- **The mean is strategy-invariant, the variance is not.**  On an unresolved
block of size at least two, the identity strategy and the constant strategy have
the same expected score `1` but different variances `1` and `0`. -/
theorem mean_invariant_variance_not (hcard : 2 ≤ Fintype.card α) (a : α) :
    (E (fun σ : Equiv.Perm α => (hits (id : α → α) σ : ℚ))
        = E (fun σ : Equiv.Perm α => (hits (fun _ => a) σ : ℚ)))
      ∧ Var (fun σ : Equiv.Perm α => (hits (id : α → α) σ : ℚ))
        ≠ Var (fun σ : Equiv.Perm α => (hits (fun _ => a) σ : ℚ)) := by
  have hne : Nonempty α := ⟨a⟩
  refine ⟨by rw [E_hits, E_hits], ?_⟩
  rw [Var_hits_injective hcard Function.injective_id, Var_hits_const a]
  norm_num

end KnownUnresolvedCards
section
open KnownUnresolvedCards
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem solution (hcard : 2 ≤ Fintype.card α) (g : α → α) :
    Var (fun σ : Equiv.Perm α => (hits g σ : ℚ))
      = (distinctCallPairs g : ℚ)
          / ((Fintype.card α : ℚ) * ((Fintype.card α : ℚ) - 1)) :=
  KnownUnresolvedCards.Var_hits_collision hcard g

end
