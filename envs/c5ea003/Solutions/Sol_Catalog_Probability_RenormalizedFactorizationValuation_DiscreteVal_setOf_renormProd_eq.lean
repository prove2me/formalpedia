-- Prove2me | solution 1 for Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal.setOf_renormProd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T13:31:17.708655+00:00
-- url     : https://prove2.me/submissions/5097a442-f690-4509-b86c-334bdcc8b6c6

import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationValuation
open Catalog.Probability.RenormalizedFactorizationValuation Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal Finset in
theorem solution {G : Type*} [CommGroup G] (V : DiscreteVal G) (k : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (d : ℕ → ℤ) :
    {g : G | ∃ f, HasProfile V m d f ∧ renormProd V k m f = g}
      = {g : G | V.val g = k + ∑ i ∈ range m, d i} := by
  -- `val (π ^ n) = n`, `val` of a product, and products of powers of `π`
  have hz : ∀ n : ℤ, V.val (V.uniformizer ^ n) = n := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, V.val_mul, ih, V.val_uniformizer]
    | pred k ih => rw [zpow_sub_one, V.val_mul, ih, V.val_inv, V.val_uniformizer]; ring
  have hvprod : ∀ (f : ℕ → G) (M : ℕ), V.val (∏ i ∈ range M, f i) = ∑ i ∈ range M, V.val (f i) := by
    intro f M
    induction M with
    | zero => simp
    | succ M ih => rw [prod_range_succ, sum_range_succ, V.val_mul, ih]
  have hzsum : ∀ (e : ℕ → ℤ) (M : ℕ),
      ∏ i ∈ range M, V.uniformizer ^ (e i) = V.uniformizer ^ (∑ i ∈ range M, e i) := by
    intro e M
    induction M with
    | zero => simp
    | succ M ih => rw [prod_range_succ, sum_range_succ, ih, zpow_add]
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · -- a renormalized product has valuation `k + Σ d`
    rintro ⟨f, ⟨hf1, -⟩, rfl⟩
    rw [renormProd, V.val_mul, hz, hvprod]
    congr 1
    exact sum_congr rfl (fun i hi => hf1 i (mem_range.mp hi))
  · -- conversely the canonical family realizes `g`
    intro hg
    refine ⟨canonFam V k m d g, ⟨fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
    · unfold canonFam
      rw [if_pos hi]
      by_cases h0 : i = 0
      · subst h0
        rw [if_pos rfl, V.val_mul, V.val_mul, hz, hz, hg]
        ring
      · rw [if_neg h0, one_mul, hz]
    · unfold canonFam
      rw [if_neg (by omega), if_neg (by omega), one_mul]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      unfold renormProd canonFam
      rw [prod_range_succ']
      have hslots : ∏ i ∈ range m',
          ((if i + 1 = 0 then V.uniformizer ^ (-(k + ∑ j ∈ range (m' + 1), d j)) * g else 1) *
            (if i + 1 < m' + 1 then V.uniformizer ^ d (i + 1) else 1))
          = ∏ i ∈ range m', V.uniformizer ^ d (i + 1) :=
        prod_congr rfl (fun i hi => by
          rw [mem_range] at hi
          rw [if_neg (by omega), if_pos (by omega), one_mul])
      rw [hslots, if_pos rfl, if_pos (by omega), hzsum (fun i => d (i + 1)), sum_range_succ']
      rw [show V.uniformizer ^ k * (V.uniformizer ^ (∑ i ∈ range m', d (i + 1)) *
            (V.uniformizer ^ (-(k + (∑ i ∈ range m', d (i + 1) + d 0))) * g * V.uniformizer ^ d 0))
          = (V.uniformizer ^ k * V.uniformizer ^ (∑ i ∈ range m', d (i + 1)) *
              V.uniformizer ^ (-(k + (∑ i ∈ range m', d (i + 1) + d 0))) * V.uniformizer ^ d 0) * g by
          ac_rfl]
      rw [← zpow_add, ← zpow_add, ← zpow_add,
        show k + ∑ i ∈ range m', d (i + 1) + -(k + (∑ i ∈ range m', d (i + 1) + d 0)) + d 0 = 0 by
          ring, zpow_zero, one_mul]
