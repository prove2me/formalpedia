-- Prove2me | Theorems.Thm_mme_coupled_binary_word_union_cardinality
-- name    : mme_coupled_binary_word_union_cardinality
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:05:27.909646+00:00
-- url     : https://prove2.me/theorems/66721068-a277-4275-abaf-454a4cc8de17
-- title:
--   Exact numeric word count for a union of binary grade patterns
-- statement:
--   Let $q,N$ be natural numbers and let $P$ be a finite set of length-$N$ patterns with entries in $\{0,1\}$. A word has letters in two disjoint copies of $\{0,\ldots,q-1\}$, and its grade pattern records which copy each letter belongs to. The number of words whose grade pattern belongs to $P$ is
--   $$|P|q^N.$$
--   Each distinct pattern contributes exactly $q^N$ independent numeric label choices. The formula counts the set of patterns, so repeated descriptions of the same pattern do not inflate the count; it also holds for empty pattern sets and zero lengths.
-- source:
--   Equivalence between each grade fiber and a product of numeric labels, followed by a disjoint sum over the pattern set.

import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Basic

open MME.DWZComponentRestriction BigOperators
universe u
set_option autoImplicit false

theorem mme_coupled_binary_word_union_cardinality (q N : ℕ)
    (patterns : Finset (Fin N → Fin 3))
    (hbinary : ∀ b ∈ patterns, ∀ r, b r = 0 ∨ b r = 1) :
    Fintype.card {w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N //
      (fun r ↦ Sum.elim (fun _ ↦ (0 : Fin 3)) (fun _ ↦ 1)
        (PowIndex.get N w r).down) ∈ patterns} = patterns.card * q ^ N := by sorry
