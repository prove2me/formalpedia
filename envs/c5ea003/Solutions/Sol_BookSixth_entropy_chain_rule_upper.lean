-- Prove2me | solution 1 for BookSixth.entropy_chain_rule_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:28:00.612244+00:00
-- url     : https://prove2.me/submissions/3f37b967-35da-41bc-bc04-017b30317dc6

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (α β : Type*) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (p : α × β → ℝ) (hnn : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    -∑ x, p x * Real.log (p x)
      ≤ -(∑ a, (∑ b, p (a, b)) * Real.log (∑ b, p (a, b)))
        + Real.log (Fintype.card β) := by
  classical
  set P : α → ℝ := fun a => ∑ b, p (a, b) with hPdef
  set C : ℝ := Real.log (Fintype.card β) with hCdef
  have hPnn : ∀ a, 0 ≤ P a :=
    fun a => Finset.sum_nonneg (fun b _ => hnn _)
  have hPsum : ∑ a, P a = 1 := by
    simp only [hPdef]
    rw [← Fintype.sum_prod_type]
    exact hsum
  -- vanishing on zero fibers
  have hzero : ∀ a, P a = 0 → ∀ b, p (a, b) = 0 := by
    intro a ha b
    have hle : p (a, b) ≤ ∑ b, p (a, b) :=
      Finset.single_le_sum (fun b _ => hnn _) (Finset.mem_univ b)
    have hPa : (∑ b, p (a, b)) = 0 := ha
    linarith [hnn (a, b)]
  -- per-term split
  have hterm : ∀ a b, p (a, b) * Real.log (p (a, b))
      = p (a, b) * Real.log (P a) + p (a, b) * Real.log (p (a, b) / P a) := by
    intro a b
    by_cases h0 : p (a, b) = 0
    · simp [h0]
    · have hPa : P a ≠ 0 := by
        intro hc
        exact h0 ((hzero a hc) b)
      rw [Real.log_div h0 hPa, mul_sub, add_sub_cancel]
  -- per-row fiber bound (negated form)
  have hfiber : ∀ a, -(∑ b, p (a, b) * Real.log (p (a, b) / P a))
      ≤ P a * C := by
    intro a
    by_cases hPa : P a = 0
    · have e : ∀ b, p (a, b) * Real.log (p (a, b) / P a) = 0 := by
        intro b
        simp [(hzero a hPa) b]
      rw [Finset.sum_congr rfl (fun b _ => e b)]
      simp [hPa]
    · have hPpos : 0 < P a := lt_of_le_of_ne' (hPnn a) hPa
      -- Jensen over the fiber support, mirroring the Shannon proof
      set S : Finset β := Finset.univ.filter (fun b => p (a, b) ≠ 0) with hS
      have hsupp : ∀ b ∈ S, 0 < p (a, b) := by
        intro b hb
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hb
        exact lt_of_le_of_ne' (hnn _) hb
      have hsumS : ∑ b ∈ S, p (a, b) / P a = 1 := by
        have hsub : ∑ b ∈ S, p (a, b) / P a = ∑ b, p (a, b) / P a := by
          apply Finset.sum_subset (Finset.subset_univ S)
          intro b _ hbS
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and,
            not_not] at hbS
          simp [hbS]
        rw [hsub, ← Finset.sum_div]
        have hPaeq : ∑ b, p (a, b) = P a := rfl
        rw [hPaeq, div_self (ne_of_gt hPpos)]
      have hconc : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
        strictConcaveOn_log_Ioi.concaveOn
      have hJ := hconc.le_map_sum (t := S) (w := fun b => p (a, b) / P a)
        (p := fun b => (p (a, b) / P a)⁻¹)
        (fun b _ => div_nonneg (hnn _) (le_of_lt hPpos)) hsumS
        (fun b hb => Set.mem_Ioi.mpr
          (inv_pos.mpr (div_pos (hsupp b hb) hPpos)))
      simp only [smul_eq_mul, Real.log_inv] at hJ
      have hsupp1 : ∀ b ∈ S, (p (a, b) / P a) * (p (a, b) / P a)⁻¹ = 1 :=
        fun b hb => mul_inv_cancel₀
          (ne_of_gt (div_pos (hsupp b hb) hPpos))
      have hcard_sum : ∑ b ∈ S, (p (a, b) / P a) * (p (a, b) / P a)⁻¹
          = (S.card : ℝ) := by
        trans ∑ _b ∈ S, (1 : ℝ)
        · exact Finset.sum_congr rfl (fun b hb => hsupp1 b hb)
        · simp
      have hLHS : ∑ b ∈ S, (p (a, b) / P a) * (-Real.log (p (a, b) / P a))
          = (P a)⁻¹ * (-∑ b, p (a, b) * Real.log (p (a, b) / P a)) := by
        have e1 : ∑ b ∈ S, (p (a, b) / P a) * (-Real.log (p (a, b) / P a))
            = ∑ b ∈ S, -((p (a, b) / P a) * Real.log (p (a, b) / P a)) :=
          Finset.sum_congr rfl (fun b _ => mul_neg _ _)
        have e2 : ∑ b ∈ S, -((p (a, b) / P a) * Real.log (p (a, b) / P a))
            = -∑ b ∈ S, (p (a, b) / P a) * Real.log (p (a, b) / P a) :=
          Finset.sum_neg_distrib _
        -- rescale below uses e4/e5
        -- rescale: (p/P) * log = (1/P) * (p * log)
        have e4 : ∀ b ∈ S, (p (a, b) / P a) * Real.log (p (a, b) / P a)
            = (P a)⁻¹ * (p (a, b) * Real.log (p (a, b) / P a)) := by
          intro b _
          rw [div_eq_mul_inv]
          ring
        -- relate full sum to fiber sum over S
        have e6 : ∑ b, p (a, b) * Real.log (p (a, b) / P a)
            = ∑ b ∈ S, p (a, b) * Real.log (p (a, b) / P a) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ S)
          intro b _ hbS
          have hb0 : p (a, b) = 0 := by
            simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and,
              not_not] at hbS
            exact hbS
          simp [hb0]
        rw [e1, e2]
        have e5 : ∑ b ∈ S, (p (a, b) / P a) * Real.log (p (a, b) / P a)
            = (P a)⁻¹ * (∑ b, p (a, b) * Real.log (p (a, b) / P a)) := by
          calc ∑ b ∈ S, (p (a, b) / P a) * Real.log (p (a, b) / P a)
              = ∑ b ∈ S, (P a)⁻¹ * (p (a, b) * Real.log (p (a, b) / P a)) :=
                Finset.sum_congr rfl (fun b hb => e4 b hb)
            _ = (P a)⁻¹ * (∑ b ∈ S, p (a, b) * Real.log (p (a, b) / P a)) :=
                (Finset.mul_sum _ _ _).symm
            _ = (P a)⁻¹ * (∑ b, p (a, b) * Real.log (p (a, b) / P a)) := by
                rw [e6]
        rw [e5, e6, mul_neg]
      rw [hcard_sum] at hJ
      rw [hLHS] at hJ
      have hcardS : S.card ≤ Fintype.card β := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ S)
      have hSne : S.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h01 : (0 : ℝ) = 1 := by
          have h2 := hsumS
          rw [hemp] at h2
          simpa using h2
        linarith
      have hpos : (0 : ℝ) < (S.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hSne
      have hGibbs : (P a)⁻¹ * (-∑ b, p (a, b) * Real.log (p (a, b) / P a))
          ≤ Real.log (S.card : ℝ) := hJ
      have hble : Real.log (S.card : ℝ) ≤ C := by
        rw [hCdef]
        exact Real.log_le_log hpos (by exact_mod_cast hcardS)
      -- scale back up by P a
      have hmul := mul_le_mul_of_nonneg_left hGibbs (le_of_lt hPpos)
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hPpos), one_mul] at hmul
      exact hmul.trans
        (mul_le_mul_of_nonneg_left hble (le_of_lt hPpos))
  -- recombine rows
  have hrow : ∀ a, ∑ b, p (a, b) * Real.log (p (a, b))
      = P a * Real.log (P a)
        + ∑ b, p (a, b) * Real.log (p (a, b) / P a) := by
    intro a
    have hPaeq : ∑ b, p (a, b) = P a := rfl
    have hconst : ∑ b, p (a, b) * Real.log (P a)
        = P a * Real.log (P a) := by
      rw [← Finset.sum_mul, hPaeq]
    calc ∑ b, p (a, b) * Real.log (p (a, b))
        = ∑ b, (p (a, b) * Real.log (P a)
          + p (a, b) * Real.log (p (a, b) / P a)) :=
          Finset.sum_congr rfl (fun b _ => hterm a b)
      _ = _ := by rw [Finset.sum_add_distrib, hconst]
  have htot : ∑ x, p x * Real.log (p x)
      = (∑ a, P a * Real.log (P a))
        + ∑ a, ∑ b, p (a, b) * Real.log (p (a, b) / P a) := by
    rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => hrow a)
  have hFbound : -(∑ a, ∑ b, p (a, b) * Real.log (p (a, b) / P a))
      ≤ Real.log (Fintype.card β) := by
    have e : ∑ a, (-(∑ b, p (a, b) * Real.log (p (a, b) / P a)))
        ≤ ∑ a, P a * C := Finset.sum_le_sum (fun a _ => hfiber a)
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hPsum, one_mul] at e
    rw [hCdef] at e
    exact e
  have hfold : ∀ a, (∑ b, p (a, b)) * Real.log (∑ b, p (a, b))
      = P a * Real.log (P a) := fun a => rfl
  rw [htot, neg_add]
  simp only [hfold]
  rw [hCdef]
  linarith [hFbound]
