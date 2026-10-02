-- Prove2me | solution 1 for ProofsInTheBook.Chapter28.chapter28_dilworth_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:10:14.147607+00:00
-- url     : https://prove2.me/submissions/3600adeb-f5d8-458f-beb7-ed4ae3d8bd52

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



theorem exists_part (𝒞 : ChainPartitionOn P) {x : α} (hx : x ∈ P) :
    ∃ C ∈ 𝒞.parts, x ∈ C :=
  (𝒞.covers' x).1 hx



end ChainPartitionOn

theorem antichain_card_le_chainPartition_card {α : Type*} [PartialOrder α] [DecidableEq α]
    {P A : Finset α} (hAP : A ⊆ P) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (𝒞 : ChainPartitionOn P) :
    A.card ≤ 𝒞.parts.card := by
  classical
  choose part hpart_mem hpart_x using fun x : A => 𝒞.exists_part (hAP x.2)
  let partOf : A → 𝒞.parts := fun x => ⟨part x, hpart_mem x⟩
  have hpart_inj : Function.Injective partOf := by
    intro x y hxy
    have hx_mem : (x : α) ∈ part x := hpart_x x
    have hpart_eq : part x = part y := congrArg Subtype.val hxy
    have hy_mem : (y : α) ∈ part x := by simpa [hpart_eq] using hpart_x y
    by_cases h : (x : α) = y
    · exact Subtype.ext h
    have hchain := 𝒞.chain' (part x) (hpart_mem x)
    rcases hchain hx_mem hy_mem h with hle | hge
    · exact Subtype.ext (hA.eq x.2 y.2 hle)
    · exact Subtype.ext (hA.eq' x.2 y.2 hge)
  simpa [partOf] using Fintype.card_le_of_injective partOf hpart_inj





end ProofsInTheBook.Chapter28

open ProofsInTheBook.Chapter28
open Finset

theorem solution {α : Type*} [Fintype α] [PartialOrder α]
    [DecidableEq α] (A : Finset α) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (𝒞 : ChainPartitionOn (univ : Finset α)) :
    A.card ≤ 𝒞.parts.card :=
  antichain_card_le_chainPartition_card (by intro x _; simp) hA 𝒞
