-- Prove2me | solution 1 for AlmostLossless.card_sum_le_card_biUnion_add_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:32:39.783181+00:00
-- url     : https://prove2.me/submissions/f46e14e4-65e8-4a9e-a6af-543f30575dcf

-- Sol generated from Geometry/AlmostLosslessConverse.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
/-
# How far beyond the pigeonhole bound can one go?  Converse and tightness

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

Two adversarial questions about the almost-lossless scheme of
`Geometry.AlmostLosslessDecoder`:

1. *How much can the counting bound really be relaxed?*
   `AlmostLossless.converse_card_good_le` — **the ε-relaxed pigeonhole bound**:
   for **any** encoder/decoder pair whatsoever, the set of strings decoded
   correctly has size at most `M`.  So a `(1-ε)`-reliable code for a typical set
   `S` still needs `M ≥ (1-ε)|S|`: relaxation buys a factor `(1-ε)`, no more.

2. *Is the `1/ε` overhead of random hashing an artefact of the union bound?*
   No.  `AlmostLossless.failure_prob_lower_bound` is a **Bonferroni lower bound**
   on the failure probability of uniform random hashing:
   `P[failure] ≥ (|S|-1) / (2M)` once `2(|S|-2) ≤ M`.
   Hence uniform random hashing genuinely needs `M ≳ |S| / ε`, a factor `Θ(1/ε)`
   above the converse — the gap is a property of the *random codebook*, not of
   the analysis.

Supporting combinatorics proved here from scratch:
* `AlmostLossless.card_sum_le_card_biUnion_add_offDiag` — the second Bonferroni
  inequality for an arbitrary finite family of finite sets.
* `AlmostLossless.card_doubleCollision_mul_le` — a two-coordinate refinement of
  the marginal count of `AlmostLosslessCore`: two prescribed collisions have
  probability `1/M²`.
-/

open AlmostLossless

open Finset

/-! ## 1. The ε-relaxed pigeonhole bound (converse) -/



/-! ## 2. Bonferroni: a lower bound for unions of finite sets -/


/-! ## 3. Two prescribed collisions have probability `1/M²` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}


/-! ## 4. The failure probability of random hashing is genuinely `≍ |S|/M` -/

variable {α : Type*} [Fintype α] [DecidableEq α]





open AlmostLossless in
theorem solution{ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    (A : ι → Finset Ω) (I : Finset ι) :
    ∑ i ∈ I, (A i).card ≤ (I.biUnion A).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
      have hunion : (A a).card + (I.biUnion A).card
          = ((insert a I).biUnion A).card + (A a ∩ I.biUnion A).card := by
        rw [Finset.biUnion_insert, ← Finset.card_union_add_card_inter]
      have hinter : (A a ∩ I.biUnion A).card ≤ ∑ i ∈ I, (A a ∩ A i).card := by
        have hEq : A a ∩ I.biUnion A = I.biUnion (fun i => A a ∩ A i) := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_biUnion]
          constructor
          · rintro ⟨hz, i, hi, hzi⟩; exact ⟨i, hi, hz, hzi⟩
          · rintro ⟨i, hi, hz, hzi⟩; exact ⟨hz, i, hi, hzi⟩
        rw [hEq]
        exact Finset.card_biUnion_le
      -- the new cross terms are among the off-diagonal pairs of `insert a I`
      have hcross : ∑ i ∈ I, (A a ∩ A i).card
          = ∑ p ∈ ({a} ×ˢ I), (A p.1 ∩ A p.2).card := by
        rw [Finset.sum_product]
        simp
      have hsubset : (I.offDiag ∪ ({a} ×ˢ I)) ⊆ (insert a I).offDiag := by
        intro p hp
        rcases Finset.mem_union.1 hp with hp | hp
        · rw [Finset.mem_offDiag] at hp ⊢
          exact ⟨mem_insert_of_mem hp.1, mem_insert_of_mem hp.2.1, hp.2.2⟩
        · rw [Finset.mem_product] at hp
          rw [Finset.mem_offDiag]
          have hp1 : p.1 = a := by simpa using hp.1
          refine ⟨by rw [hp1]; exact mem_insert_self a I, mem_insert_of_mem hp.2, ?_⟩
          rw [hp1]
          intro hcon
          exact ha (hcon ▸ hp.2)
      have hdisj : Disjoint I.offDiag ({a} ×ˢ I) := by
        rw [Finset.disjoint_left]
        intro p hp hp'
        rw [Finset.mem_offDiag] at hp
        rw [Finset.mem_product] at hp'
        have : p.1 = a := by simpa using hp'.1
        exact ha (this ▸ hp.1)
      have hsum : ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card
            + ∑ p ∈ ({a} ×ˢ I), (A p.1 ∩ A p.2).card
          ≤ ∑ p ∈ (insert a I).offDiag, (A p.1 ∩ A p.2).card := by
        rw [← Finset.sum_union hdisj]
        exact Finset.sum_le_sum_of_subset hsubset
      calc ∑ i ∈ insert a I, (A i).card = (A a).card + ∑ i ∈ I, (A i).card := by
            rw [Finset.sum_insert ha]
        _ ≤ (A a).card + ((I.biUnion A).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card) := by
            omega
        _ = ((insert a I).biUnion A).card + (A a ∩ I.biUnion A).card
              + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by omega
        _ ≤ ((insert a I).biUnion A).card + ∑ i ∈ I, (A a ∩ A i).card
              + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by omega
        _ = ((insert a I).biUnion A).card
              + (∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card
                 + ∑ p ∈ ({a} ×ˢ I), (A p.1 ∩ A p.2).card) := by rw [hcross]; omega
        _ ≤ ((insert a I).biUnion A).card
              + ∑ p ∈ (insert a I).offDiag, (A p.1 ∩ A p.2).card := by omega
