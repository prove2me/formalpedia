-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter28
-- name    : ProofsInTheBook_Chapter28
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T15:57:24.286175+00:00
-- url     : https://prove2.me/theorems/66855c1d-7df6-4845-81d8-39a8c1e2621d
-- title:
--   Finite chain partitions of a specified ordered set
-- statement:
--   Let $X$ be a type with a relation $\le$, and let $P\subseteq X$ be finite. A `ChainPartitionOn P` consists of a finite family $\mathcal C$ of finite subsets of $X$ such that every member is a chain, distinct members are disjoint, and
--   $$x\in P\quad\Longleftrightarrow\quad\exists C\in\mathcal C,\ x\in C.$$
--   A chain means any two distinct members are comparable under $\le$. No total-order or partial-order laws are included in this structure, and nonemptiness of each part is not required.
--
--   The structure represents the given chain decomposition only; it contains no optimality condition or equality between chain count and antichain size.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 30, “Three famous theorems on finite sets”, pp. 213–217 (https://doi.org/10.1007/978-3-662-57265-8_30). Original definition source: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter28.lean#L75. The generated bundle retains definitions and supporting declarations from this source; the book citation identifies their topic rather than asserting that each auxiliary structure appears in the book.

import Mathlib

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

structure ChainPartitionOn {α : Type*} [LE α] (P : Finset α) where
  parts : Finset (Finset α)
  chain' : ∀ C ∈ parts, IsChain (· ≤ ·) (C : Set α)
  disjoint' : ∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D
  covers' : ∀ x, x ∈ P ↔ ∃ C ∈ parts, x ∈ C

namespace ChainPartitionOn

variable {α : Type*} [LE α] {P : Finset α}







end ChainPartitionOn







end ProofsInTheBook.Chapter28


