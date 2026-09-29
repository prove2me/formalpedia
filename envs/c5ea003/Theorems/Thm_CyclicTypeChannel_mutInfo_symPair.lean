-- Prove2me | Theorems.Thm_CyclicTypeChannel_mutInfo_symPair
-- name    : CyclicTypeChannel.mutInfo_symPair
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:27:18.52724+00:00
-- url     : https://prove2.me/theorems/d6d5086e-a8e5-47cc-be9b-7c020b2913ff
-- title:
--   The which-factor wall is exactly zero.
-- statement:
--   **The which-factor wall is exactly zero.**  Forgetting which of the two
--   components carries which value costs the same entropy with or without knowing
--   the conditioning variable, so the *channel* is unchanged.
--
--   ```lean
--   theorem CyclicTypeChannel.mutInfo_symPair{γ : Type*} [DecidableEq γ] {k : α → γ} (hσs : ∀ a ∈ s, σ a ∈ s)
--       (hσσ : ∀ a ∈ s, σ (σ a) = a) (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1))
--       (hkσ : ∀ a ∈ s, k (σ a) = k a) :
--       mutInfo s (symPair ∘ g) k = mutInfo s g k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelSymmetry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelSymmetry.lean#L180

-- Thm stub generated from Shared/CyclicTypeChannelSymmetry.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
/-
# The which-factor wall is exactly zero

A semiprime `N = p q` presents its two prime factors symmetrically: nothing in
`N mod f` can say *which* factor carries which splitting type.  Experimentally
the "which-factor" information was measured at `0.0001` bits, i.e. zero.

This file proves that it is **exactly** zero, in complete generality:  for any
sample set carrying an involution `σ` which swaps the two components of the
read-out and fixes the conditioning variable, forgetting the order of the two
components changes both the entropy and the conditional entropy by *the same*
amount, namely the probability of an off-diagonal pair.  Consequently the
mutual information of the unordered read-out equals that of the ordered one.

The entropies themselves are genuinely different (the ordered pair carries
strictly more entropy whenever off-diagonal pairs occur); it is only the
*channel* that is insensitive to the ordering.
-/

open CyclicTypeChannel

open Finset


variable {α β : Type*} [LinearOrder β]



variable [DecidableEq β] {s : Finset α} {g : α → β × β} {σ : α → α}

theorem CyclicTypeChannel.mutInfo_symPair{γ : Type*} [DecidableEq γ] {k : α → γ} (hσs : ∀ a ∈ s, σ a ∈ s)
    (hσσ : ∀ a ∈ s, σ (σ a) = a) (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1))
    (hkσ : ∀ a ∈ s, k (σ a) = k a) :
    mutInfo s (symPair ∘ g) k = mutInfo s g k := by sorry
