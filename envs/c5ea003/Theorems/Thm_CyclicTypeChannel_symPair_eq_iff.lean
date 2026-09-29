-- Prove2me | Theorems.Thm_CyclicTypeChannel_symPair_eq_iff
-- name    : CyclicTypeChannel.symPair_eq_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:27:13.958805+00:00
-- url     : https://prove2.me/theorems/7f427dce-1eb3-4c6f-b474-1fa2a055a29c
-- title:
--   Two ordered pairs have the same unordered shadow exactly when they agree, or
-- statement:
--   Two ordered pairs have the same unordered shadow exactly when they agree, or
--   agree after a swap.
--
--   ```lean
--   theorem CyclicTypeChannel.symPair_eq_iff(z w : β × β) :
--       symPair z = symPair w ↔ z = w ∨ z = (w.2, w.1) := by sorry
--   variable [DecidableEq β] {s : Finset α} {g : α → β × β} {σ : α → α}
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelSymmetry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelSymmetry.lean#L31

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

theorem CyclicTypeChannel.symPair_eq_iff(z w : β × β) :
    symPair z = symPair w ↔ z = w ∨ z = (w.2, w.1) := by sorry
