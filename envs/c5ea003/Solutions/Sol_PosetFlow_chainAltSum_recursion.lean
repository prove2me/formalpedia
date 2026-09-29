-- Prove2me | solution 1 for PosetFlow.chainAltSum_recursion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:50:20.354822+00:00
-- url     : https://prove2.me/submissions/1de4494c-2d80-49b3-9fa6-74dd47987740

-- Sol generated from Algebra/PosetFlow/HallMobius.lean
import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_HallMobius
import Theorems.Thm_PosetFlow_exists_greatest_of_total
import Theorems.Thm_PosetFlow_mem_chainFinsets

/-!
# Philip Hall's theorem: chains of a poset compute its Möbius function

The chain replacement of a poset flow replaces the (one point) spaces of execution
paths of a poset flow by the nerves of the refinement posets of chains.  The Euler
characteristics of those nerves are governed by the classical theorem of Philip
Hall, which identifies the alternating sum over chains from `x` to `y` with the
Möbius function of the incidence algebra.

This file proves Hall's theorem in the form

`∑ C ∈ chainFinsets x y, (-1) ^ |C| = - μ x y`,

where `chainFinsets x y` is the finite set of carriers of chains from `x` to `y`
(the objects of the refinement poset `PosetFlow.ChainFrom x y` of
`Algebra.PosetFlow.ChainPoset`), and `μ` is `IncidenceAlgebra.mu`.

## Main results

* `PosetFlow.chainAltSum_recursion` : deleting the top element `y` of a chain
  identifies chains from `x` to `y` with pairs `(z, C)` where `z ∈ Ico x y` and `C`
  is a chain from `x` to `z`.  This is the combinatorial induction step.
* `PosetFlow.chainAltSum_eq_neg_mu` : **Philip Hall's theorem**.
* `PosetFlow.mu_eq_zero_of_not_le` : the Möbius function vanishes off the order,
  a corollary of the chain description.
-/

open PosetFlow

open Finset IncidenceAlgebra

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]











variable [LocallyFiniteOrder P]






open PosetFlow in
theorem solution{x y : P} (hxy : x < y) :
    chainAltSum x y = -∑ z ∈ Finset.Ico x y, chainAltSum x z := by
  have key : ∑ p ∈ (Finset.Ico x y).sigma (fun z => chainFinsets x z),
      (-1 : ℤ) ^ (insert y p.2).card = ∑ C ∈ chainFinsets x y, (-1 : ℤ) ^ C.card := by
    refine Finset.sum_nbij (fun p => insert y p.2) ?_ ?_ ?_ ?_
    · -- the map lands in the chains from `x` to `y`
      rintro ⟨z, C⟩ hp
      dsimp only
      simp only [Finset.mem_sigma] at hp
      obtain ⟨hz, hC⟩ := hp
      rw [Finset.mem_Ico] at hz
      rw [mem_chainFinsets] at hC
      obtain ⟨h1, h2, h3, h4⟩ := hC
      rw [mem_chainFinsets]
      refine ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_self _ _, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.1 ha with hay | ha
        · exact ⟨by rw [hay]; exact le_of_lt hxy, le_of_eq hay⟩
        · exact ⟨(h3 a ha).1, le_trans (h3 a ha).2 (le_of_lt hz.2)⟩
      · intro a ha b hb
        rcases Finset.mem_insert.1 ha with hay | ha
        · rcases Finset.mem_insert.1 hb with hby | hb
          · exact Or.inl (by rw [hay, hby])
          · exact Or.inr (by rw [hay]; exact le_trans (h3 b hb).2 (le_of_lt hz.2))
        · rcases Finset.mem_insert.1 hb with hby | hb
          · exact Or.inl (by rw [hby]; exact le_trans (h3 a ha).2 (le_of_lt hz.2))
          · exact h4 a ha b hb
    · -- injectivity
      rintro ⟨z, C⟩ hp ⟨z', C'⟩ hp' heq
      dsimp only at heq
      simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_Ico] at hp hp'
      obtain ⟨hz, hC⟩ := hp
      obtain ⟨hz', hC'⟩ := hp'
      rw [mem_chainFinsets] at hC hC'
      have hyC : y ∉ C := fun hy => absurd (hC.2.2.1 y hy).2 (not_le_of_gt hz.2)
      have hyC' : y ∉ C' := fun hy => absurd (hC'.2.2.1 y hy).2 (not_le_of_gt hz'.2)
      have hCC' : C = C' := by
        apply Finset.Subset.antisymm
        · intro a ha
          have hmem : a ∈ insert y C' := by rw [← heq]; exact Finset.mem_insert_of_mem ha
          rcases Finset.mem_insert.1 hmem with hay | h
          · exact absurd (hay ▸ ha) hyC
          · exact h
        · intro a ha
          have hmem : a ∈ insert y C := by rw [heq]; exact Finset.mem_insert_of_mem ha
          rcases Finset.mem_insert.1 hmem with hay | h
          · exact absurd (hay ▸ ha) hyC'
          · exact h
      subst hCC'
      have h1 : z' ≤ z := (hC.2.2.1 z' hC'.2.1).2
      have h2 : z ≤ z' := (hC'.2.2.1 z hC.2.1).2
      simp [le_antisymm h2 h1]
    · -- surjectivity: every chain from `x` to `y` arises this way
      intro C hC
      rw [Finset.mem_coe, mem_chainFinsets] at hC
      obtain ⟨h1, h2, h3, h4⟩ := hC
      have hne : (C.erase y).Nonempty := ⟨x, Finset.mem_erase.2 ⟨ne_of_lt hxy, h1⟩⟩
      obtain ⟨z, hzmem, hzmax⟩ := exists_greatest_of_total (C.erase y) hne
        (fun a ha b hb => h4 a (Finset.mem_erase.1 ha).2 b (Finset.mem_erase.1 hb).2)
      have hzC : z ∈ C := (Finset.mem_erase.1 hzmem).2
      have hzne : z ≠ y := (Finset.mem_erase.1 hzmem).1
      have hzlt : z < y := lt_of_le_of_ne (h3 z hzC).2 hzne
      have hxz : x ≤ z := (h3 z hzC).1
      have hCz : C.erase y ∈ chainFinsets x z := by
        rw [mem_chainFinsets]
        refine ⟨Finset.mem_erase.2 ⟨ne_of_lt hxy, h1⟩, hzmem, ?_, ?_⟩
        · intro a ha
          exact ⟨(h3 a (Finset.mem_erase.1 ha).2).1, hzmax a ha⟩
        · intro a ha b hb
          exact h4 a (Finset.mem_erase.1 ha).2 b (Finset.mem_erase.1 hb).2
      refine ⟨⟨z, C.erase y⟩, ?_, ?_⟩
      · simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_Ico]
        exact ⟨⟨hxz, hzlt⟩, hCz⟩
      · exact Finset.insert_erase h2
    · -- the summands agree
      rintro ⟨z, C⟩ _
      rfl
  have hcard : ∀ p ∈ (Finset.Ico x y).sigma (fun z => chainFinsets x z),
      (-1 : ℤ) ^ (insert y p.2).card = -((-1 : ℤ) ^ p.2.card) := by
    rintro ⟨z, C⟩ hp
    rw [Finset.mem_sigma, Finset.mem_Ico] at hp
    obtain ⟨hz, hC⟩ := hp
    rw [mem_chainFinsets] at hC
    have hyC : y ∉ C := fun hy => absurd (hC.2.2.1 y hy).2 (not_le_of_gt hz.2)
    rw [Finset.card_insert_of_notMem hyC, pow_succ]
    ring
  rw [chainAltSum, ← key, Finset.sum_congr rfl hcard, Finset.sum_neg_distrib]
  congr 1
  rw [show (∑ z ∈ Finset.Ico x y, chainAltSum x z)
      = ∑ z ∈ Finset.Ico x y, ∑ C ∈ chainFinsets x z, (-1 : ℤ) ^ C.card from rfl,
    Finset.sum_sigma']
