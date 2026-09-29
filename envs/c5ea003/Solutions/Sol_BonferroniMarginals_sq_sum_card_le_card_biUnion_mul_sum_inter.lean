-- Prove2me | solution 1 for BonferroniMarginals.sq_sum_card_le_card_biUnion_mul_sum_inter
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T07:57:58.804976+00:00
-- url     : https://prove2.me/submissions/29641251-0d57-444b-8d70-d71901b66770

import Mathlib
import Definitions.Def_Geometry_BonferroniMarginals
open BonferroniMarginals Finset in
theorem solution {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    (A : ι → Finset Ω) (I : Finset ι) :
    (∑ i ∈ I, (A i).card) ^ 2
      ≤ (I.biUnion A).card * ∑ p ∈ I ×ˢ I, (A p.1 ∩ A p.2).card := by
  set U := I.biUnion A with hU
  -- multiplicity of a point: `d ω = #{i ∈ I : ω ∈ A i}`
  let d : Ω → ℕ := fun ω => (I.filter (fun i => ω ∈ A i)).card
  have hd : ∀ ω, d ω = ∑ i ∈ I, if ω ∈ A i then 1 else 0 := fun ω => (sum_boole _ _).symm
  -- first moment: `Σ |A i| = Σ_ω d ω`
  have h1 : ∑ i ∈ I, (A i).card = ∑ ω ∈ U, d ω := by
    have hA : ∀ i ∈ I, (A i).card = ∑ ω ∈ U, if ω ∈ A i then 1 else 0 := by
      intro i hi
      rw [sum_boole, filter_mem_eq_inter, inter_eq_right.mpr (subset_biUnion_of_mem A hi)]
      rfl
    rw [sum_congr rfl hA, sum_comm]
    exact sum_congr rfl fun ω _ => (hd ω).symm
  -- second moment: `Σ_{i,j} |A i ∩ A j| = Σ_ω d ω²`
  have h2 : ∑ p ∈ I ×ˢ I, (A p.1 ∩ A p.2).card = ∑ ω ∈ U, d ω ^ 2 := by
    have hA : ∀ p ∈ I ×ˢ I, (A p.1 ∩ A p.2).card
        = ∑ ω ∈ U, (if ω ∈ A p.1 then 1 else 0) * (if ω ∈ A p.2 then 1 else 0) := by
      intro p hp
      rw [mem_product] at hp
      have hsub : A p.1 ∩ A p.2 ⊆ U := inter_subset_left.trans (subset_biUnion_of_mem A hp.1)
      simp_rw [ite_zero_mul_ite_zero, mul_one]
      rw [sum_boole]
      congr 1
      ext ω
      simp only [mem_filter, mem_inter]
      constructor
      · intro h
        exact ⟨hsub (mem_inter.mpr h), h⟩
      · rintro ⟨-, h⟩
        exact h
    rw [sum_congr rfl hA, sum_comm]
    refine sum_congr rfl fun ω _ => ?_
    rw [sum_product, hd, sq, sum_mul_sum]
  rw [h1, h2]
  exact sq_sum_le_card_mul_sum_sq
