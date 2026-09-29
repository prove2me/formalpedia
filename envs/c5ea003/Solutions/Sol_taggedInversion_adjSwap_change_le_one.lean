-- Prove2me | solution 1 for taggedInversion_adjSwap_change_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:26:26.891262+00:00
-- url     : https://prove2.me/submissions/a46d128f-7f26-45ed-91e8-14a545d28b69

-- Sol generated from Bridges/GraphTheory/TaggedCardTASEP.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_TaggedCardTASEP
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Tagged-Card TASEP Structure in Permutation Random Walks

This file formalizes the first rigorous bridge between permutation random walks
on S_n (driven by adjacent transpositions and long cycles) and the theory of
driven diffusive systems, specifically the Totally Asymmetric Simple Exclusion
Process (TASEP) and KPZ universality.

## Core idea
The adjacent-transposition-plus-cycle walk on S_n contains two competing
mechanisms:
- **local exclusion-like transport** from adjacent swaps
- **deterministic global drift** from the long cycle

A single labeled ("tagged") card therefore behaves as a tagged excitation in
a driven diffusive medium. We formalize tractable finite-n versions of this
observation and prove nontrivial drift/variance/current identities.

## Convention
We use the RIGHT multiplication convention for position swaps:
  τ = σ * swap(i, i')
means "swap the cards at positions i and i'". Under this convention:
  taggedCardPos(τ, j) = swap(i, i')(σ⁻¹(j))
so card j moves if and only if its current position σ⁻¹(j) equals i or i'.

## Main definitions

* `taggedCardPos` — position of card j under permutation σ (i.e., σ⁻¹(j))
* `taggedSignedIncrement` — signed displacement of card j in one step
* `taggedInversionCount` — number of cards k > j sitting left of j
* `TaggedCardEnvironment` — structure for drift decomposition

## Main results

* `taggedCard_drift_decomposition` — increment is +1, -1, or 0
* `taggedSignedIncrement_sq_le_one` — per-step squared increment ≤ 1
* `taggedInversion_adjSwap_change_le_one` — inversion count changes by ≤ 1
* `taggedIncrement_zero_preserves_inversions` — zero increment ⟹ no inversion change

## Application keywords
driven diffusive systems, tagged particle, TASEP, KPZ universality,
current fluctuations, permutation random walk, Cayley graph dynamics,
exclusion process, nonequilibrium statistical mechanics, algebraic combinatorics,
inversion current, integrable probability, Tracy–Widom fluctuations,
hydrodynamic scaling, spectral gap, martingale decomposition
-/

open Finset BigOperators Equiv Equiv.Perm

/-! ## Basic definitions -/





/-! ## Swap mechanics: position changes under right-multiplication by swap -/

/-
Key identity: for τ = σ * swap(i, i'), the position of card j is
    obtained by applying swap(i, i') to the old position σ⁻¹(j).
    This is because τ⁻¹ = swap(i,i') * σ⁻¹.
-/

/-
If card j is not at position i or i', it doesn't move.
-/

/-
If card j is at position i, swapping positions (i, i') moves it to i'.
-/

/-
If card j is at position i', swapping positions (i, i') moves it to i.
-/

/-! ## Theorem 1: Drift decomposition for a tagged card -/

/-
**Theorem 1 (Drift decomposition).**
    For the walk on S_n, each step swaps the cards at positions (i, i+1).
    The signed increment of tagged card j decomposes:

    - If card j is at position i: increment = +1 (card moves right)
    - If card j is at position i+1: increment = -1 (card moves left)
    - Otherwise: increment = 0 (card unaffected)

    This is the fundamental finite-n current identity. The expected drift
    over uniform choice of swap edge decomposes as:
      E[Δ_j | σ] = (1/(n-1)) · (𝟙_{pos can move right} - 𝟙_{pos can move left})
    which is the cycle-drift + swap-correction decomposition.
-/

/-! ## Theorem 2: Per-step squared increment bound -/

/-
**Theorem 2 (Per-step variance bound — squared increment ≤ 1).**
    Each adjacent-swap step changes card j's position by at most 1
    in absolute value. Therefore the squared increment is ≤ 1.

    This is the finite-n analog of the TASEP nearest-neighbor constraint.
    It implies Var(pos_j(X_t)) ≤ t for the raw position process.
-/

/-
Absolute value version: |Δ_j| ≤ 1 for each adjacent swap step.
-/

/-! ## Theorem 3: Inversion count change controlled -/

/-
**Theorem 3 (Cross-domain: inversion count bounded change).**
    For an adjacent swap of positions (i, i+1), the tagged inversion count
    of card j changes by at most 1. Swapping positions i and i+1 can only
    affect inversions involving the two cards σ(i) and σ(i+1), and at most
    one such inversion involves card j.

    This establishes the algebraic-combinatorial bridge: displacement
    becomes an order statistic, connecting to RSK correspondence,
    growth models, and random matrix asymptotics.
-/

/-! ## Theorem 4: Increment-inversion bridge -/

/-
**Theorem 4 (Increment determines inversion change).**
    When card j is not involved in the swap (increment = 0),
    the inversion count is preserved. This connects the transport
    observable (displacement) to the combinatorial observable (inversions).

    The key insight: if card j doesn't move, its relative ordering with
    every other card is unchanged. The two cards that DO swap are at
    adjacent positions, so their relative order with respect to j
    (which is elsewhere) is determined by their positions relative to j,
    which doesn't change when j stays put.
-/

/-! ## KPZ/TASEP Conjecture (formally stated) -/


theorem solution{n : ℕ} (hn : 2 ≤ n)
    (j : Fin n) (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (hi : i.val + 1 < n) :
    let i' : Fin n := ⟨i.val + 1, hi⟩
    let τ := σ * Equiv.swap i i'
    |taggedInversionCount j τ - taggedInversionCount j σ| ≤ 1 := by
  refine' abs_sub_le_iff.mpr _;
  constructor <;> rw [ taggedInversionCount, taggedInversionCount ];
  · rw [ sub_le_iff_le_add' ];
    refine' mod_cast le_trans ( Finset.card_le_card _ ) _;
    exact Finset.filter ( fun k => j < k ∧ σ⁻¹ k < σ⁻¹ j ) Finset.univ ∪ { if σ⁻¹ j = i then σ ⟨ i + 1, hi ⟩ else if σ⁻¹ j = ⟨ i + 1, hi ⟩ then σ i else j };
    · intro k hk; simp_all +decide [ Finset.subset_iff, Equiv.swap_apply_def ] ;
      grind;
    · exact Finset.card_union_le _ _;
  · refine' sub_le_iff_le_add'.mpr _;
    refine' mod_cast Nat.le_of_lt_succ ( _ );
    refine' lt_of_le_of_lt ( Finset.card_mono _ ) _;
    exact Finset.filter ( fun k => j < k ∧ ( σ * swap i ⟨ i + 1, hi ⟩ ) ⁻¹ k < ( σ * swap i ⟨ i + 1, hi ⟩ ) ⁻¹ j ) Finset.univ ∪ { σ ( swap i ⟨ i + 1, hi ⟩ ( σ⁻¹ j ) ) };
    · intro k hk; by_cases hk' : k = σ ( swap i ⟨ i + 1, hi ⟩ ( σ⁻¹ j ) ) <;> simp_all +decide [ Finset.subset_iff ] ;
      grind +revert;
    · exact lt_of_le_of_lt ( Finset.card_union_le _ _ ) ( Nat.add_lt_add_right ( Nat.lt_succ_self _ ) _ )
