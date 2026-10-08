-- Prove2me | solution 1 for ProofsInTheBook.Chapter28.chapter28_erdos_ko_rado
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:10:15.728526+00:00
-- url     : https://prove2.me/submissions/d82c4841-e836-4e28-bf1a-4a3918b3c4dd

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter28


/-!
# Chapter 28: Three famous theorems on finite sets

From "Proofs from THE BOOK":

1. **Sperner's theorem**: The largest antichain in 𝒫([n]) has C(n,⌊n/2⌋) sets.
2. **Erdős-Ko-Rado**: For n ≥ 2k, a k-uniform intersecting family has ≤ C(n-1,k-1) sets.
3. **Dilworth's theorem**: min chain cover = max antichain.

The book proves Sperner via the **LYM inequality**: for an antichain 𝒜 ⊆ 𝒫([n]),
  ∑_{A ∈ 𝒜} 1/C(n,|A|) ≤ 1.
Since each C(n,|A|) ≤ C(n,⌊n/2⌋), this gives |𝒜| ≤ C(n,⌊n/2⌋).

Formalization status:
* Sperner is proved below from Mathlib's LYM inequality.
* Erdős-Ko-Rado is proved by calling Mathlib's Kruskal-Katona based theorem.
* Mathlib has no ready-made Dilworth/Kőnig chain-cover theorem in this checkout.
  This file proves the universal lower bound `antichain.card ≤ chainPartition.card`;
  the reverse chain-partition construction remains the honest missing part of
  Dilworth rather than being hidden behind an axiom or a theorem-shaped premise.
-/

namespace ProofsInTheBook.Chapter28

open Finset

/-!
### Erdős-Ko-Rado

Mathlib already contains the Kruskal-Katona proof of Erdős-Ko-Rado for
families of `r`-subsets of `Fin n`.  The book's hypothesis `2r ≤ n` is
converted to Mathlib's `r ≤ n / 2`.
-/



/-!
### Sperner's theorem via LYM

An antichain in the power set of a finite type α (ordered by ⊆)
has at most C(|α|, ⌊|α|/2⌋) elements.
-/



/-!
### Dilworth's theorem

The definitions below use chain partitions of a finite set.  For a partition
of the ground set into chains, any antichain meets each part in at most one
point, so the antichain size is bounded by the number of chains.  The reverse
inequality is the hard half of Dilworth.
-/



namespace ChainPartitionOn

variable {α : Type*} [LE α] {P : Finset α}







end ChainPartitionOn







end ProofsInTheBook.Chapter28

open ProofsInTheBook.Chapter28
open Finset

theorem solution {n r : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (hr : (𝒜 : Set (Finset (Fin n))).Sized r) (hn : 2 * r ≤ n) :
    𝒜.card ≤ (n - 1).choose (r - 1) := by
  exact Finset.erdos_ko_rado h𝒜 hr (by omega)
