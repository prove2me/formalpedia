-- Prove2me | solution 1 for chain_cover_card_ge_middle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:09:58.574923+00:00
-- url     : https://prove2.me/submissions/fa418824-1d25-496b-ab75-9c06810b9c60

-- Sol generated from Logic/PosetTheory/SpernerChainCover.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_SpernerChainCover
/-
# A Chain-Cover Lower Bound for the Boolean Lattice

This file proves a lower bound on the number of chains needed to cover the
Boolean lattice `Finset (Fin n)`: any family of chains whose union covers every
subset of `Fin n` must contain at least `n.choose (n / 2)` chains.

The argument is the "easy half" of Dilworth-type reasoning specialised to the
Boolean lattice: the middle layer (all subsets of size `n / 2`) is an antichain
of size `n.choose (n / 2)`, and any chain meets an antichain in at most one
element, so at least `n.choose (n / 2)` chains are required.

## Note on the statement

The requested statement declared `𝒞 : Finset (Finset (Fin n))`.  That type is not
consistent with the hypotheses: `h_chain` asks each `C ∈ 𝒞` to be a *chain* of
subsets, i.e. `C : Finset (Finset (Fin n))` (coerced to `Set (Finset (Fin n))`),
and `h_cover` asks `s : Finset (Fin n)` to be a *member* of some `C ∈ 𝒞`.  Both
force each element of `𝒞` to be a `Finset (Finset (Fin n))`, hence
`𝒞 : Finset (Finset (Finset (Fin n)))`.  We use this corrected, type-correct
type for `𝒞`.
-/

open Finset

variable {n : ℕ}


/-- A chain and an antichain (both with respect to `⊆`) intersect in at most one
element. -/
lemma chain_inter_antichain_card_le_one
    {C A : Finset (Finset (Fin n))}
    (hC : IsChain (· ⊆ ·) (C : Set (Finset (Fin n))))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset (Fin n)))) :
    (C ∩ A).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  obtain ⟨haC, haA⟩ := ha
  obtain ⟨hbC, hbA⟩ := hb
  by_contra hne
  rcases hC haC hbC hne with h | h
  · exact hA haA hbA hne h
  · exact hA hbA haA (Ne.symm hne) h

/-- The middle layer is an antichain with respect to `⊆`. -/
lemma middleLayer_isAntichain :
    IsAntichain (· ⊆ ·) (middleLayer n : Set (Finset (Fin n))) := by
  intro s hs t ht hne hsub
  simp only [Finset.coe_filter, Set.mem_setOf_eq, middleLayer, Finset.mem_univ,
    true_and] at hs ht
  exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [hs, ht]))

/-- The middle layer has cardinality `n.choose (n / 2)`. -/
lemma middleLayer_card : (middleLayer n).card = n.choose (n / 2) := by
  have : middleLayer n = Finset.powersetCard (n / 2) (Finset.univ : Finset (Fin n)) := by
    ext s; simp [middleLayer, Finset.mem_powersetCard]
  rw [this, Finset.card_powersetCard]; simp


theorem solution    {𝒞 : Finset (Finset (Finset (Fin n)))}
    (h_chain : ∀ C ∈ 𝒞, IsChain (· ⊆ ·) (C : Set (Finset (Fin n))))
    (h_cover : ∀ s : Finset (Fin n), ∃ C ∈ 𝒞, s ∈ C) :
    𝒞.card ≥ n.choose (n / 2) := by
  -- Step 2: each chain meets the middle layer (an antichain) in at most one element.
  have h1 : ∀ C ∈ 𝒞, (C ∩ middleLayer n).card ≤ 1 := fun C hC =>
    chain_inter_antichain_card_le_one (h_chain C hC) middleLayer_isAntichain
  -- Step 3: the middle layer is covered by the pieces `C ∩ middleLayer n`.
  have hsub : middleLayer n ⊆ 𝒞.biUnion (fun C => C ∩ middleLayer n) := by
    intro s hs
    obtain ⟨C, hC, hsC⟩ := h_cover s
    rw [Finset.mem_biUnion]
    exact ⟨C, hC, Finset.mem_inter.mpr ⟨hsC, hs⟩⟩
  have h3 : (middleLayer n).card ≤ ∑ C ∈ 𝒞, (C ∩ middleLayer n).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  -- Step 4: combine the bounds.
  calc n.choose (n / 2) = (middleLayer n).card := middleLayer_card.symm
    _ ≤ ∑ C ∈ 𝒞, (C ∩ middleLayer n).card := h3
    _ ≤ ∑ _C ∈ 𝒞, 1 := Finset.sum_le_sum h1
    _ = 𝒞.card := by simp
