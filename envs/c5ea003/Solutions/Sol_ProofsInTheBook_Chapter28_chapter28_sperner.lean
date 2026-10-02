-- Prove2me | solution 1 for ProofsInTheBook.Chapter28.chapter28_sperner
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:10:17.169441+00:00
-- url     : https://prove2.me/submissions/c1a3c53f-11d6-4395-ad63-af34545a8ea9

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

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 : Finset (Finset α))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) :=
  by
    have hmiddle_pos : 0 < ((Fintype.card α).choose (Fintype.card α / 2) : ℚ≥0) :=
      Nat.cast_pos.2 <| Nat.choose_pos (Nat.div_le_self _ _)
    have hlym := calc
      ∑ s ∈ 𝒜, ((Fintype.card α).choose (Fintype.card α / 2) : ℚ≥0)⁻¹
        ≤ ∑ s ∈ 𝒜, ((Fintype.card α).choose #s : ℚ≥0)⁻¹ := by
          gcongr with s hs
          · exact mod_cast Nat.choose_pos s.card_le_univ
          · exact Nat.choose_le_middle _ _
      _ ≤ 1 := Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose h𝒜
    simpa [mul_inv_le_iff₀' hmiddle_pos] using hlym
