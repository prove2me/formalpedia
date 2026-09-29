-- Prove2me | solution 1 for MarkovMixing.tv_coupling
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:03:20.666205+00:00
-- url     : https://prove2.me/submissions/ca7107e9-6a52-4b18-aef0-780a4106ae80

import Theorems.Thm_MarkovMixing_tv_eq_half_l1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) :
    (∀ q : V × V → ℝ, IsCoupling μ ν q →
      tvDist μ ν ≤ ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ≠ p.2), q p) ∧
    ∃ q : V × V → ℝ, IsCoupling μ ν q ∧
      tvDist μ ν = ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ≠ p.2), q p := by
  classical
  set s : ℝ := tvDist μ ν with hsdef
  have hprop := MarkovMixing.tv_eq_half_l1 μ ν hμ hν
  have hl1 : ∑ x, |μ x - ν x| = 2 * s := by rw [hsdef, hprop.1]; ring
  have hs_nonneg : 0 ≤ s := by
    have : (0:ℝ) ≤ ∑ x, |μ x - ν x| :=
      Finset.sum_nonneg fun x _ => abs_nonneg _
    linarith
  have hbdd : BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    Set.Finite.bddAbove
      (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  -- the excess mass of μ over ν
  have hexcess : ∑ x, (μ x - min (μ x) (ν x)) = s := by
    have hpt : ∀ x : V, μ x - min (μ x) (ν x) = (|μ x - ν x| + (μ x - ν x)) / 2 := by
      intro x
      rcases le_total (ν x) (μ x) with h | h
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    rw [Finset.sum_congr rfl fun x _ => hpt x]
    have hz : ∑ x, (μ x - ν x) = 0 := by
      rw [Finset.sum_sub_distrib, hμ.2, hν.2, sub_self]
    have hsplit : ∑ x, (|μ x - ν x| + (μ x - ν x)) / 2
        = (∑ x, |μ x - ν x| + ∑ x, (μ x - ν x)) / 2 := by
      rw [← Finset.sum_add_distrib]
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    rw [hsplit, hl1, hz]
    ring
  have hexcess' : ∑ x, (ν x - min (μ x) (ν x)) = s := by
    have hpt : ∀ x : V, ν x - min (μ x) (ν x) = (|μ x - ν x| - (μ x - ν x)) / 2 := by
      intro x
      rcases le_total (ν x) (μ x) with h | h
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    rw [Finset.sum_congr rfl fun x _ => hpt x]
    have hz : ∑ x, (μ x - ν x) = 0 := by
      rw [Finset.sum_sub_distrib, hμ.2, hν.2, sub_self]
    have hsplit : ∑ x, (|μ x - ν x| - (μ x - ν x)) / 2
        = (∑ x, |μ x - ν x| - ∑ x, (μ x - ν x)) / 2 := by
      rw [← Finset.sum_sub_distrib]
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    rw [hsplit, hl1, hz]
    ring
  have hminsum : ∑ x, min (μ x) (ν x) = 1 - s := by
    have h := hexcess
    rw [Finset.sum_sub_distrib, hμ.2] at h
    linarith
  have hme_nonneg : ∀ x : V, 0 ≤ μ x - min (μ x) (ν x) := fun x => by
    have := min_le_left (μ x) (ν x); linarith
  have hne_nonneg : ∀ x : V, 0 ≤ ν x - min (μ x) (ν x) := fun x => by
    have := min_le_right (μ x) (ν x); linarith
  have hprod0 : ∀ x : V, (μ x - min (μ x) (ν x)) * (ν x - min (μ x) (ν x)) = 0 := by
    intro x
    rcases le_total (ν x) (μ x) with h | h
    · rw [min_eq_right h]; ring
    · rw [min_eq_left h]; ring
  constructor
  · -- every coupling puts at least `s` mass off the diagonal
    intro q hq
    refine ciSup_le fun A => ?_
    have hA1 : ∑ p : V × V, q p * (if p.1 ∈ A then (1:ℝ) else 0) = ∑ x ∈ A, μ x := by
      rw [Fintype.sum_prod_type]
      have h : ∀ x : V, (∑ y, q (x, y) * (if x ∈ A then (1:ℝ) else 0))
          = (if x ∈ A then μ x else 0) := by
        intro x
        by_cases hx : x ∈ A
        · simp only [if_pos hx, mul_one]; exact hq.2.1 x
        · simp only [if_neg hx, mul_zero]; exact Finset.sum_const_zero
      rw [Finset.sum_congr rfl fun x _ => h x]
      simp
    have hA2 : ∑ p : V × V, q p * (if p.2 ∈ A then (1:ℝ) else 0) = ∑ y ∈ A, ν y := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      have h : ∀ y : V, (∑ x, q (x, y) * (if y ∈ A then (1:ℝ) else 0))
          = (if y ∈ A then ν y else 0) := by
        intro y
        by_cases hy : y ∈ A
        · simp only [if_pos hy, mul_one]; exact hq.2.2 y
        · simp only [if_neg hy, mul_zero]; exact Finset.sum_const_zero
      rw [Finset.sum_congr rfl fun y _ => h y]
      simp
    have hdiff : ∑ x ∈ A, μ x - ∑ x ∈ A, ν x
        = ∑ p : V × V, q p
            * ((if p.1 ∈ A then (1:ℝ) else 0) - (if p.2 ∈ A then (1:ℝ) else 0)) := by
      rw [← hA1, ← hA2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hdiff]
    have hstep : ∀ p : V × V,
        |q p * ((if p.1 ∈ A then (1:ℝ) else 0) - (if p.2 ∈ A then (1:ℝ) else 0))|
        ≤ (if p.1 ≠ p.2 then q p else 0) := by
      intro p
      by_cases hp : p.1 = p.2
      · have h1 : (if p.1 ∈ A then (1:ℝ) else 0) - (if p.2 ∈ A then (1:ℝ) else 0) = 0 := by
          rw [hp]; ring
        rw [h1, mul_zero, abs_zero, if_neg (not_not.mpr hp)]
      · rw [if_pos hp, abs_mul, abs_of_nonneg (hq.1.1 p)]
        have hle : |(if p.1 ∈ A then (1:ℝ) else 0) - (if p.2 ∈ A then (1:ℝ) else 0)| ≤ 1 := by
          by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ A <;>
            simp [h1, h2]
        calc q p * |(if p.1 ∈ A then (1:ℝ) else 0) - (if p.2 ∈ A then (1:ℝ) else 0)|
            ≤ q p * 1 := mul_le_mul_of_nonneg_left hle (hq.1.1 p)
          _ = q p := mul_one _
    calc |∑ p : V × V, q p
            * ((if p.1 ∈ A then (1:ℝ) else 0) - (if p.2 ∈ A then (1:ℝ) else 0))|
        ≤ ∑ p : V × V, |q p
            * ((if p.1 ∈ A then (1:ℝ) else 0) - (if p.2 ∈ A then (1:ℝ) else 0))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : V × V, (if p.1 ≠ p.2 then q p else 0) :=
          Finset.sum_le_sum fun p _ => hstep p
      _ = ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ≠ p.2), q p :=
          (Finset.sum_filter _ _).symm
  · -- the optimal coupling
    set a : V → ℝ := fun x => μ x - min (μ x) (ν x) with hadef
    set b : V → ℝ := fun x => ν x - min (μ x) (ν x) with hbdef
    set q : V × V → ℝ :=
      fun p => if p.1 = p.2 then min (μ p.1) (ν p.1) else a p.1 * b p.2 / s with hqdef
    have ha_sum : ∑ x, a x = s := hexcess
    have hb_sum : ∑ x, b x = s := hexcess'
    have ha_nonneg : ∀ x, 0 ≤ a x := hme_nonneg
    have hb_nonneg : ∀ x, 0 ≤ b x := hne_nonneg
    have hab0 : ∀ x, a x * b x = 0 := hprod0
    have ha_zero : s = 0 → ∀ x, a x = 0 := by
      intro h0 x
      by_contra hx
      have hpos : 0 < a x := lt_of_le_of_ne (ha_nonneg x) (Ne.symm hx)
      have := Finset.single_le_sum (f := a) (fun y _ => ha_nonneg y) (Finset.mem_univ x)
      rw [ha_sum, h0] at this
      linarith
    have hb_zero : s = 0 → ∀ x, b x = 0 := by
      intro h0 x
      by_contra hx
      have hpos : 0 < b x := lt_of_le_of_ne (hb_nonneg x) (Ne.symm hx)
      have := Finset.single_le_sum (f := b) (fun y _ => hb_nonneg y) (Finset.mem_univ x)
      rw [hb_sum, h0] at this
      linarith
    have hcancel_a : ∀ x : V, a x * s / s = a x := by
      intro x
      rcases eq_or_lt_of_le hs_nonneg with h0 | hpos
      · rw [← h0, ha_zero h0.symm x]; simp
      · field_simp
    have hcancel_b : ∀ y : V, s * b y / s = b y := by
      intro y
      rcases eq_or_lt_of_le hs_nonneg with h0 | hpos
      · rw [← h0, hb_zero h0.symm y]; simp
      · field_simp
    have hq_diag : ∀ x : V, q (x, x) = min (μ x) (ν x) := by
      intro x; rw [hqdef]; simp
    have hq_off : ∀ x y : V, x ≠ y → q (x, y) = a x * b y / s := by
      intro x y hxy; rw [hqdef]; simp only; rw [if_neg hxy]
    -- row sums
    have hrow : ∀ x : V, ∑ y, q (x, y) = μ x := by
      intro x
      have hdiffsum : ∑ y, (q (x, y) - a x * b y / s)
          = min (μ x) (ν x) - a x * b x / s := by
        rw [Finset.sum_eq_single x]
        · rw [hq_diag x]
        · intro y _ hy
          rw [hq_off x y (Ne.symm hy), sub_self]
        · intro hc; exact absurd (Finset.mem_univ x) hc
      rw [Finset.sum_sub_distrib] at hdiffsum
      have hbsum : ∑ y, a x * b y / s = a x * s / s := by
        simp only [div_eq_mul_inv, mul_assoc, ← Finset.mul_sum]
        rw [← Finset.sum_mul, hb_sum]
      rw [hbsum, hcancel_a x] at hdiffsum
      have hz : a x * b x / s = 0 := by rw [hab0 x, zero_div]
      rw [hz, sub_zero] at hdiffsum
      have : ∑ y, q (x, y) = a x + min (μ x) (ν x) := by linarith
      rw [this, hadef]
      simp
    -- column sums
    have hcol : ∀ y : V, ∑ x, q (x, y) = ν y := by
      intro y
      have hdiffsum : ∑ x, (q (x, y) - a x * b y / s)
          = min (μ y) (ν y) - a y * b y / s := by
        rw [Finset.sum_eq_single y]
        · rw [hq_diag y]
        · intro x _ hx
          rw [hq_off x y hx, sub_self]
        · intro hc; exact absurd (Finset.mem_univ y) hc
      rw [Finset.sum_sub_distrib] at hdiffsum
      have hasum : ∑ x, a x * b y / s = s * b y / s := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        rw [ha_sum]
      rw [hasum, hcancel_b y] at hdiffsum
      have hz : a y * b y / s = 0 := by rw [hab0 y, zero_div]
      rw [hz, sub_zero] at hdiffsum
      have : ∑ x, q (x, y) = b y + min (μ y) (ν y) := by linarith
      rw [this, hbdef]
      simp
    have hq_nonneg : ∀ p : V × V, 0 ≤ q p := by
      intro p
      by_cases hp : p.1 = p.2
      · rw [hqdef]; simp only; rw [if_pos hp]
        exact le_min (hμ.1 p.1) (hν.1 p.1)
      · rw [hq_off p.1 p.2 hp]
        exact div_nonneg (mul_nonneg (ha_nonneg p.1) (hb_nonneg p.2)) hs_nonneg
    have htotal : ∑ p : V × V, q p = 1 := by
      rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun x _ => hrow x]
      exact hμ.2
    refine ⟨q, ⟨⟨hq_nonneg, htotal⟩, hrow, hcol⟩, ?_⟩
    -- the off-diagonal mass is exactly the total variation distance
    have hoff : ∀ x : V, (∑ y, if x ≠ y then q (x, y) else 0) = a x := by
      intro x
      have hrewrite : ∀ y : V,
          (if x ≠ y then q (x, y) else 0) = q (x, y) - (if x = y then q (x, y) else 0) := by
        intro y
        by_cases hxy : x = y
        · rw [if_neg (not_not.mpr hxy), if_pos hxy, sub_self]
        · rw [if_pos hxy, if_neg hxy, sub_zero]
      rw [Finset.sum_congr rfl fun y _ => hrewrite y, Finset.sum_sub_distrib,
        Finset.sum_ite_eq Finset.univ x (fun y => q (x, y)), if_pos (Finset.mem_univ x),
        hrow x, hq_diag x, hadef]
    rw [Finset.sum_filter, Fintype.sum_prod_type,
      Finset.sum_congr rfl fun x _ => hoff x, ha_sum]
