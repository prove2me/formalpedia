-- Prove2me | solution 1 for MarkovMixing.tv_le_sep
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:22:21.98285+00:00
-- url     : https://prove2.me/submissions/2501c4b9-7054-4435-80ff-294f57711eeb

import Theorems.Thm_MarkovMixing_tv_eq_half_l1
import Definitions.Def_mm_stopping
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hpos : ∀ y : V, 0 < π y)
    (x : V) (t : ℕ) :
    tvDist (rowDist P t x) π ≤ sepDist P π x t := by
  classical
  have hpow_nonneg : ∀ (n : ℕ) (a b : V), 0 ≤ (P ^ n) a b := by
    intro n
    induction n with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ m ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hP.1 w b)
  have hpow_row : ∀ (n : ℕ) (a : V), ∑ b, (P ^ n) a b = 1 := by
    intro n
    induction n with
    | zero => intro a; simp [Matrix.one_apply]
    | succ m ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ m * P) a b = ∑ w, (P ^ m) a w * P w b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum, hP.2 w, mul_one]]
        exact ih a
  set μ : V → ℝ := rowDist P t x with hμdef
  have hμ : IsDist μ := ⟨fun y => hpow_nonneg t x y, hpow_row t x⟩
  -- the separation distance dominates each of its defining terms
  have hbdd : BddAbove (Set.range fun y : V => 1 - (P ^ t) x y / π y) :=
    Set.Finite.bddAbove (Set.range fun y : V => 1 - (P ^ t) x y / π y).toFinite
  have hsep_ge : ∀ y : V, 1 - μ y / π y ≤ sepDist P π x t := fun y => le_ciSup hbdd y
  -- the separation distance is nonnegative
  have hsep_nonneg : 0 ≤ sepDist P π x t := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ y : V, π y < μ y := by
      intro y
      have h := hsep_ge y
      have h1 : 1 - μ y / π y < 0 := lt_of_le_of_lt h hcon
      have h2 : 1 < μ y / π y := by linarith
      rw [lt_div_iff₀ (hpos y)] at h2
      linarith
    have hsum : (1:ℝ) < 1 := by
      calc (1:ℝ) = ∑ y, π y := hπ.1.2.symm
        _ < ∑ y, μ y := Finset.sum_lt_sum_of_nonempty ⟨x, Finset.mem_univ x⟩
              (fun y _ => hall y)
        _ = 1 := hμ.2
    linarith
  -- total variation as the deficit of `μ` relative to `π`
  have hprop := MarkovMixing.tv_eq_half_l1 μ π hμ hπ.1
  set S : Finset V := Finset.univ.filter (fun y : V => μ y < π y) with hS
  have hzero : ∑ y, (μ y - π y) = 0 := by
    rw [Finset.sum_sub_distrib, hμ.2, hπ.1.2, sub_self]
  have hsplit : tvDist μ π = ∑ y ∈ S, (π y - μ y) := by
    have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun y : V => π y ≤ μ y) (fun y => μ y - π y)
    have hSeq : Finset.univ.filter (fun y : V => ¬ (π y ≤ μ y)) = S := by
      rw [hS]
      apply Finset.filter_congr
      intro y _
      constructor
      · intro h; linarith [not_le.mp h]
      · intro h; exact not_le.mpr h
    rw [hSeq] at hpart
    rw [← hprop.2, hzero] at hpart
    have hneg : ∑ y ∈ S, (μ y - π y) = -(∑ y ∈ S, (π y - μ y)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hneg] at hpart
    linarith
  rw [hsplit]
  -- bound each deficit term by `π y` times the separation distance
  calc ∑ y ∈ S, (π y - μ y) = ∑ y ∈ S, π y * (1 - μ y / π y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        have hy : π y ≠ 0 := (hpos y).ne'
        field_simp
    _ ≤ ∑ y ∈ S, π y * sepDist P π x t :=
        Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hsep_ge y) (hpos y).le
    _ = (∑ y ∈ S, π y) * sepDist P π x t := by rw [← Finset.sum_mul]
    _ ≤ 1 * sepDist P π x t := by
        refine mul_le_mul_of_nonneg_right ?_ hsep_nonneg
        rw [← hπ.1.2]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun y _ _ => hπ.1.1 y)
    _ = sepDist P π x t := one_mul _
