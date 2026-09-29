-- Prove2me | solution 1 for BonferroniMarginals.card_biUnion_lower_of_marginals
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:29:51.130895+00:00
-- url     : https://prove2.me/submissions/70712257-c22f-4e0e-a5e0-cbc38ff2d4e2

import Mathlib
import Definitions.Def_Geometry_BonferroniMarginals
open BonferroniMarginals Finset in
theorem solution {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    (A : ι → Finset Ω) (I : Finset ι) {m c N : ℕ} (hN : 0 < N)
    (hmarg : ∀ i ∈ I, m * (A i).card = N)
    (hpair : ∀ p ∈ I.offDiag, c * (A p.1 ∩ A p.2).card ≤ N) :
    c * I.card * N ≤ m * (I.biUnion A).card * (c + m * (I.card - 1)) := by
  -- Bonferroni / Cauchy–Schwarz: `(Σ |A i|)² ≤ |⋃ A i| · Σ_{i,j} |A i ∩ A j|`
  have hB : (∑ i ∈ I, (A i).card) ^ 2
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
  set k := I.card with hk
  set U := (I.biUnion A).card with hU
  -- the pair sum splits into the diagonal and the off-diagonal
  have hdiag : ∑ p ∈ I ×ˢ I, (A p.1 ∩ A p.2).card
      = ∑ i ∈ I, (A i).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by
    rw [← diag_union_offDiag, sum_union (disjoint_diag_offDiag I)]
    congr 1
    rw [diag, sum_map]
    simp
  have hsumA : m * ∑ i ∈ I, (A i).card = k * N := by
    rw [mul_sum, sum_congr rfl hmarg, sum_const, smul_eq_mul]
  have hoff : c * ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card ≤ k * (k - 1) * N := by
    rw [mul_sum]
    calc ∑ p ∈ I.offDiag, c * (A p.1 ∩ A p.2).card ≤ ∑ _p ∈ I.offDiag, N := sum_le_sum hpair
      _ = k * (k - 1) * N := by
          rw [sum_const, smul_eq_mul, offDiag_card, Nat.mul_sub_one]
  have key : c * k * N * (k * N) ≤ m * U * (c + m * (k - 1)) * (k * N) := by
    calc c * k * N * (k * N) = c * (m * ∑ i ∈ I, (A i).card) ^ 2 := by rw [hsumA]; ring
      _ = c * m ^ 2 * (∑ i ∈ I, (A i).card) ^ 2 := by ring
      _ ≤ c * m ^ 2 * (U * (∑ i ∈ I, (A i).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card)) :=
          Nat.mul_le_mul_left _ (hdiag ▸ hB)
      _ = m * U * (c * (m * ∑ i ∈ I, (A i).card) + m * (c * ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card)) := by
          ring
      _ ≤ m * U * (c * (k * N) + m * (k * (k - 1) * N)) := by
          rw [hsumA]
          exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hoff) _)
      _ = m * U * (c + m * (k - 1)) * (k * N) := by ring
  rcases Nat.eq_zero_or_pos k with h0 | hkpos
  · rw [h0]
    simp
  · exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hkpos hN)
