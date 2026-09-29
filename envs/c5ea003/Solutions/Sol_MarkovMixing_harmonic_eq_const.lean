-- Prove2me | solution 1 for MarkovMixing.harmonic_eq_const
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:12:20.971581+00:00
-- url     : https://prove2.me/submissions/8bd330a8-5d47-47c8-9c73-299b551b8d3f

import Definitions.Def_mm_basic

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (h : V → ℝ) (hh : Harmonic P h) (x y : V) :
    h x = h y := by
  haveI : Nonempty V := ⟨x⟩
  have hpow_nonneg : ∀ (t : ℕ) (a b : V), 0 ≤ (P ^ t) a b := by
    intro t
    induction t with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih a z) (hP.1 z b)
  have hpow_row : ∀ (t : ℕ) (a : V), ∑ b, (P ^ t) a b = 1 := by
    intro t
    induction t with
    | zero => intro a; simp [Matrix.one_apply]
    | succ n ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ n * P) a b = ∑ z, (P ^ n) a z * P z b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun z _ => by rw [← Finset.mul_sum, hP.2 z, mul_one]]
        exact ih a
  have hharm_pow : ∀ (t : ℕ) (a : V), h a = ∑ b, (P ^ t) a b * h b := by
    intro t
    induction t with
    | zero => intro a; simp [Matrix.one_apply]
    | succ n ih =>
        intro a
        rw [pow_succ]
        have hmul : ∀ z : V, (P ^ n * P) a z = ∑ b, (P ^ n) a b * P b z := fun z => rfl
        rw [Finset.sum_congr rfl fun z _ => by rw [hmul z]]
        have expand : ∑ z, (∑ b, (P ^ n) a b * P b z) * h z
            = ∑ b, (P ^ n) a b * ∑ z, P b z * h z := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun z _ => by ring
        rw [expand]
        rw [ih a]
        exact Finset.sum_congr rfl fun b _ => by rw [← hh b]
  obtain ⟨x₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) h Finset.univ_nonempty
  have hmax' : ∀ z : V, h z ≤ h x₀ := fun z => hmax z (Finset.mem_univ z)
  have key : ∀ (t : ℕ) (z : V), 0 < (P ^ t) x₀ z → h z = h x₀ := by
    intro t z hz
    have hle : ∀ b ∈ (Finset.univ : Finset V),
        (P ^ t) x₀ b * h b ≤ (P ^ t) x₀ b * h (x₀) :=
      fun b _ => mul_le_mul_of_nonneg_left (hmax' b) (hpow_nonneg t x₀ b)
    have hEq : ∑ b, (P ^ t) x₀ b * h b = ∑ b, (P ^ t) x₀ b * h x₀ := by
      rw [← hharm_pow t x₀, ← Finset.sum_mul, hpow_row t x₀, one_mul]
    have hptw := (Finset.sum_eq_sum_iff_of_le hle).mp hEq z (Finset.mem_univ z)
    exact mul_left_cancel₀ hz.ne' hptw
  obtain ⟨t₁, ht₁⟩ := hirr x₀ x
  obtain ⟨t₂, ht₂⟩ := hirr x₀ y
  rw [key t₁ x ht₁, key t₂ y ht₂]
