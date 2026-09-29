-- Prove2me | solution 2 for Catalog.Probability.RenormalizedFactorizationValuation.padic_rigidity_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T13:36:06.420513+00:00
-- url     : https://prove2.me/submissions/79400bb4-9710-4ce3-a27d-7f12f1c2a686

import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationValuation
open Catalog.Probability.RenormalizedFactorizationValuation Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal Finset HahnSeries in
theorem solution (p : ℕ) [hp : Fact p.Prime] (k : ℤ) (m : ℕ) (hm : 1 ≤ m) (d : ℕ → ℤ)
    (g : (ℚ_[p])ˣ)
    (hg : Padic.valuation (p := p) (g : ℚ_[p]) = k + ∑ i ∈ range m, d i) :
    (DiscreteVal.factorizations (padicVal p) k m d g).Subsingleton ↔ m = 1 := by
  obtain ⟨V, hV⟩ : ∃ V, V = padicVal p := ⟨_, rfl⟩
  rw [← hV]
  replace hg : V.val g = k + ∑ i ∈ range m, d i := by rw [hV]; exact hg
  -- the unit `-1` has valuation `0` and is not `1`
  obtain ⟨u, hu, hu1⟩ : ∃ u : (ℚ_[p])ˣ, V.val u = 0 ∧ u ≠ 1 := by
    refine ⟨-1, ?_, ?_⟩
    · have h := V.val_mul (-1) (-1)
      rw [neg_one_mul, neg_neg, V.val_one] at h
      omega
    · intro h
      have h' := congrArg Units.val h
      simp only [Units.val_neg, Units.val_one] at h'
      norm_num at h'
  -- `val (π ^ n) = n`
  have hz : ∀ n : ℤ, V.val (V.uniformizer ^ n) = n := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, V.val_mul, ih, V.val_uniformizer]
    | pred k ih => rw [zpow_sub_one, V.val_mul, ih, V.val_inv, V.val_uniformizer]; ring
  have hzsum : ∀ (e : ℕ → ℤ) (M : ℕ),
      ∏ i ∈ range M, V.uniformizer ^ (e i) = V.uniformizer ^ (∑ i ∈ range M, e i) := by
    intro e M
    induction M with
    | zero => simp
    | succ M ih => rw [prod_range_succ, sum_range_succ, ih, zpow_add]
  -- the canonical factorization lies in the fibre
  have hcanon : canonFam V k m d g ∈ factorizations V k m d g := by
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
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
  constructor
  · -- for `m ≥ 2`, twisting slots `0, 1` by `u, u⁻¹` gives a second factorization
    intro hsub
    by_contra hm1
    obtain ⟨m'', rfl⟩ : ∃ m'', m = m'' + 2 := ⟨m - 2, by omega⟩
    have hf₁ : (fun i => canonFam V k (m'' + 2) d g i *
        (if i = 0 then u else if i = 1 then u⁻¹ else 1)) ∈ factorizations V k (m'' + 2) d g := by
      refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
      · show V.val (canonFam V k (m'' + 2) d g i * (if i = 0 then u else if i = 1 then u⁻¹ else 1))
          = d i
        rw [V.val_mul, hcanon.1.1 i hi]
        split_ifs <;> simp [hu]
      · show canonFam V k (m'' + 2) d g i * (if i = 0 then u else if i = 1 then u⁻¹ else 1) = 1
        rw [hcanon.1.2 i hi, if_neg (by omega), if_neg (by omega), mul_one]
      · show renormProd V k (m'' + 2) (fun i => canonFam V k (m'' + 2) d g i *
            (if i = 0 then u else if i = 1 then u⁻¹ else 1)) = g
        have ht : ∏ i ∈ range (m'' + 2), (if i = 0 then u else if i = 1 then u⁻¹ else 1) = 1 := by
          rw [prod_range_succ', prod_range_succ']
          rw [prod_eq_one (fun i _ => by rw [if_neg (by omega), if_neg (by omega)])]
          simp
        unfold renormProd
        rw [prod_mul_distrib, ht, mul_one]
        exact hcanon.2
    have h0 := congrFun (hsub hcanon hf₁) 0
    simp only [if_pos] at h0
    exact hu1 (mul_left_cancel (h0.symm.trans (mul_one _).symm))
  · -- for `m = 1` slot `0` is forced to be `π^(-k) g`
    rintro rfl
    intro f hf f' hf'
    funext i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h1 := hf.2
      have h2 := hf'.2
      unfold renormProd at h1 h2
      simp only [range_one, prod_singleton] at h1 h2
      exact mul_left_cancel (h1.trans h2.symm)
    · rw [hf.1.2 i hi, hf'.1.2 i hi]
