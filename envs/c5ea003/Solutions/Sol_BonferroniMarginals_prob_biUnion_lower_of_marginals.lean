-- Prove2me | solution 1 for BonferroniMarginals.prob_biUnion_lower_of_marginals
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T01:18:12.245007+00:00
-- url     : https://prove2.me/submissions/be962050-ef9f-4013-a2ea-169c1a8d3df2

import Mathlib
import Definitions.Def_Geometry_BonferroniMarginals
open Finset in
theorem solution {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    (A : ι → Finset Ω) (I : Finset ι) {m c N : ℕ} (hN : 0 < N) (hm : 0 < m)
    (hc : 0 < c) (hmarg : ∀ i ∈ I, m * (A i).card = N)
    (hpair : ∀ p ∈ I.offDiag, c * (A p.1 ∩ A p.2).card ≤ N) :
    (c : ℝ) * I.card / ((m : ℝ) * (c + m * ((I.card : ℝ) - 1)))
      ≤ ((I.biUnion A).card : ℝ) / N := by
  rcases I.eq_empty_or_nonempty with hI | hI
  · subst hI
    simp
  -- multiplicity of a point in the union
  have hsub : ∀ i ∈ I, A i ⊆ I.biUnion A := fun i hi x hx => mem_biUnion.2 ⟨i, hi, hx⟩
  -- first moment: `Σ_x d(x) = Σ_i |A_i|`
  have h1 : ∑ x ∈ I.biUnion A, ((I.filter (fun i => x ∈ A i)).card : ℝ)
      = ∑ i ∈ I, ((A i).card : ℝ) := by
    have : ∀ x, ((I.filter (fun i => x ∈ A i)).card : ℝ)
        = ∑ i ∈ I, if x ∈ A i then (1 : ℝ) else 0 := by
      intro x
      rw [card_filter]
      push_cast
      rfl
    simp only [this]
    rw [sum_comm]
    refine sum_congr rfl (fun i hi => ?_)
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext x
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun hx => hsub i hi hx
  -- second moment: `Σ_x d(x)² = Σ_i Σ_j |A_i ∩ A_j|`
  have h2 : ∑ x ∈ I.biUnion A, ((I.filter (fun i => x ∈ A i)).card : ℝ) ^ 2
      = ∑ i ∈ I, ∑ j ∈ I, ((A i ∩ A j).card : ℝ) := by
    have : ∀ x, ((I.filter (fun i => x ∈ A i)).card : ℝ) ^ 2
        = ∑ i ∈ I, ∑ j ∈ I, if x ∈ A i ∩ A j then (1 : ℝ) else 0 := by
      intro x
      rw [card_filter, sq]
      push_cast
      rw [sum_mul_sum]
      refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
      by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j <;> simp [hi, hj]
    simp only [this]
    rw [sum_comm]
    refine sum_congr rfl (fun i hi => ?_)
    rw [sum_comm]
    refine sum_congr rfl (fun j _ => ?_)
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext x
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun hx => hsub i hi (mem_inter.1 hx).1
  -- plug in the marginals
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hAi : ∀ i ∈ I, ((A i).card : ℝ) = N / m := by
    intro i hi
    rw [eq_div_iff hmR.ne']
    have := hmarg i hi
    rw [mul_comm]
    exact_mod_cast this
  have hS1 : ∑ i ∈ I, ((A i).card : ℝ) = I.card * (N / m) := by
    rw [sum_congr rfl hAi, sum_const, nsmul_eq_mul]
  have hS2 : ∑ i ∈ I, ∑ j ∈ I, ((A i ∩ A j).card : ℝ)
      ≤ I.card * (N / m) + I.card * ((I.card : ℝ) - 1) * (N / c) := by
    have hrow : ∀ i ∈ I, ∑ j ∈ I, ((A i ∩ A j).card : ℝ)
        ≤ N / m + ((I.card : ℝ) - 1) * (N / c) := by
      intro i hi
      rw [← add_sum_erase I _ hi, inter_self, hAi i hi]
      have hle : ∑ j ∈ I.erase i, ((A i ∩ A j).card : ℝ) ≤ ∑ j ∈ I.erase i, (N / c : ℝ) := by
        refine sum_le_sum (fun j hj => ?_)
        have hp := hpair (i, j) (mem_offDiag.2 ⟨hi, mem_of_mem_erase hj, (ne_of_mem_erase hj).symm⟩)
        rw [le_div_iff₀ hcR, mul_comm]
        exact_mod_cast hp
      rw [sum_const, card_erase_of_mem hi, nsmul_eq_mul,
        Nat.cast_sub (card_pos.2 hI), Nat.cast_one] at hle
      linarith
    calc ∑ i ∈ I, ∑ j ∈ I, ((A i ∩ A j).card : ℝ)
        ≤ ∑ i ∈ I, (N / m + ((I.card : ℝ) - 1) * (N / c)) := sum_le_sum hrow
      _ = I.card * (N / m) + I.card * ((I.card : ℝ) - 1) * (N / c) := by
          rw [sum_const, nsmul_eq_mul]
          ring
  -- Cauchy–Schwarz: `(Σ d)² ≤ |U| Σ d²`
  have hcs := sq_sum_le_card_mul_sum_sq (s := I.biUnion A)
    (f := fun x => ((I.filter (fun i => x ∈ A i)).card : ℝ))
  rw [h1, h2, hS1] at hcs
  have hk : (1 : ℝ) ≤ I.card := by exact_mod_cast card_pos.2 hI
  have hU0 : (0 : ℝ) ≤ (I.biUnion A).card := Nat.cast_nonneg _
  have hmain : ((I.card : ℝ) * (N / m)) ^ 2
      ≤ (I.biUnion A).card * (I.card * (N / m) + I.card * ((I.card : ℝ) - 1) * (N / c)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hS2 hU0)
  have hden : 0 < (m : ℝ) * (c + m * ((I.card : ℝ) - 1)) := by
    apply mul_pos hmR
    nlinarith
  rw [div_le_div_iff₀ hden hNR]
  -- clear denominators in `hmain`
  have e1 : ((I.card : ℝ) * (N / m)) ^ 2 * (m ^ 2 * c) = (I.card : ℝ) ^ 2 * N ^ 2 * c := by
    field_simp
  have e2 : (I.card * (N / m) + I.card * ((I.card : ℝ) - 1) * (N / c)) * (m ^ 2 * c)
      = (I.card : ℝ) * N * m * (c + m * ((I.card : ℝ) - 1)) := by
    field_simp
  have hmc : 0 < (m : ℝ) ^ 2 * c := by positivity
  have h3 : (I.card : ℝ) ^ 2 * N ^ 2 * c
      ≤ (I.biUnion A).card * ((I.card : ℝ) * N * m * (c + m * ((I.card : ℝ) - 1))) := by
    calc (I.card : ℝ) ^ 2 * N ^ 2 * c = ((I.card : ℝ) * (N / m)) ^ 2 * (m ^ 2 * c) := e1.symm
      _ ≤ (I.biUnion A).card * (I.card * (N / m) + I.card * ((I.card : ℝ) - 1) * (N / c))
          * (m ^ 2 * c) := mul_le_mul_of_nonneg_right hmain hmc.le
      _ = (I.biUnion A).card * ((I.card * (N / m) + I.card * ((I.card : ℝ) - 1) * (N / c))
          * (m ^ 2 * c)) := by ring
      _ = (I.biUnion A).card * ((I.card : ℝ) * N * m * (c + m * ((I.card : ℝ) - 1))) := by
          rw [e2]
  -- divide by `|I| N > 0`
  have hIN : 0 < (I.card : ℝ) * N := by positivity
  have h4 : ((I.card : ℝ) * N) * (c * I.card * N)
      ≤ ((I.card : ℝ) * N) * ((I.biUnion A).card * (m * (c + m * ((I.card : ℝ) - 1)))) := by
    calc ((I.card : ℝ) * N) * (c * I.card * N) = (I.card : ℝ) ^ 2 * N ^ 2 * c := by ring
      _ ≤ (I.biUnion A).card * ((I.card : ℝ) * N * m * (c + m * ((I.card : ℝ) - 1))) := h3
      _ = ((I.card : ℝ) * N) * ((I.biUnion A).card * (m * (c + m * ((I.card : ℝ) - 1)))) := by
          ring
  exact le_of_mul_le_mul_left h4 hIN
