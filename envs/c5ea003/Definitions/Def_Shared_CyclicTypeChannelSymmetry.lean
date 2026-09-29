-- Prove2me | Definitions.Def_Shared_CyclicTypeChannelSymmetry
-- name    : Shared_CyclicTypeChannelSymmetry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:36.903011+00:00
-- url     : https://prove2.me/theorems/1c33afa8-4c70-4f47-8f58-d20b3da6e0b6
-- title:
--   Aether Catalog definitions — Shared_CyclicTypeChannelSymmetry
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CyclicTypeChannelSymmetry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CyclicTypeChannelSymmetry.lean by skeleton subtraction
import Mathlib
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

namespace CyclicTypeChannel

open Finset

section Symmetrization

variable {α β : Type*} [LinearOrder β]

/-- Forget the order of an ordered pair. -/
def symPair (z : β × β) : β × β := (min z.1 z.2, max z.1 z.2)


variable [DecidableEq β] {s : Finset α} {g : α → β × β} {σ : α → α}






end Symmetrization

end CyclicTypeChannel


