-- Prove2me | Theorems.Thm_CyclicTypeChannel_condEnt_symPair
-- name    : CyclicTypeChannel.condEnt_symPair
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:27:32.938418+00:00
-- url     : https://prove2.me/theorems/652bd900-66f4-490c-a4ee-77766e456ec6
-- title:
--   The conditional entropy defect is the same.
-- statement:
--   **The conditional entropy defect is the same.**  If the involution also fixes
--   the conditioning variable, conditioning does not change the cost of forgetting
--   the order.
--
--   ```lean
--   theorem CyclicTypeChannel.condEnt_symPair{γ : Type*} [DecidableEq γ] {k : α → γ} (hσs : ∀ a ∈ s, σ a ∈ s)
--       (hσσ : ∀ a ∈ s, σ (σ a) = a) (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1))
--       (hkσ : ∀ a ∈ s, k (σ a) = k a) :
--       condEnt s (symPair ∘ g) k = condEnt s g k - (#{a ∈ s | (g a).1 ≠ (g a).2} : ℝ) / s.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelSymmetry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelSymmetry.lean#L133

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

theorem CyclicTypeChannel.condEnt_symPair{γ : Type*} [DecidableEq γ] {k : α → γ} (hσs : ∀ a ∈ s, σ a ∈ s)
    (hσσ : ∀ a ∈ s, σ (σ a) = a) (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1))
    (hkσ : ∀ a ∈ s, k (σ a) = k a) :
    condEnt s (symPair ∘ g) k = condEnt s g k - (#{a ∈ s | (g a).1 ≠ (g a).2} : ℝ) / s.card := by sorry
