-- Prove2me | Theorems.Thm_CyclicTypeChannel_card_swap_fiber
-- name    : CyclicTypeChannel.card_swap_fiber
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:27:00.567396+00:00
-- url     : https://prove2.me/theorems/1788e48d-4fd1-4228-b01a-21a801e2365e
-- title:
--   The swapped fibre has the same size as the fibre: the involution `Ï` maps one
-- statement:
--   The swapped fibre has the same size as the fibre: the involution `Ï` maps one
--   onto the other.
--
--   ```lean
--   theorem CyclicTypeChannel.card_swap_fiber(hσs : ∀ a ∈ s, σ a ∈ s) (hσσ : ∀ a ∈ s, σ (σ a) = a)
--       (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1)) (a : α) :
--       (#{x ∈ s | g x = ((g a).2, (g a).1)}) = #{x ∈ s | g x = g a} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelSymmetry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelSymmetry.lean#L50

-- Thm stub generated from Shared/CyclicTypeChannelSymmetry.lean
import Mathlib
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

omit [LinearOrder β] in

theorem CyclicTypeChannel.card_swap_fiber(hσs : ∀ a ∈ s, σ a ∈ s) (hσσ : ∀ a ∈ s, σ (σ a) = a)
    (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1)) (a : α) :
    (#{x ∈ s | g x = ((g a).2, (g a).1)}) = #{x ∈ s | g x = g a} := by sorry
