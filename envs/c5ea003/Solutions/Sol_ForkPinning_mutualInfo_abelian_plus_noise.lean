-- Prove2me | solution 1 for ForkPinning.mutualInfo_abelian_plus_noise
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:18:19.097927+00:00
-- url     : https://prove2.me/submissions/8d03d739-69f9-4703-ac21-7fb940f4d82a

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningProduct
open ForkPinning Finset Real in
theorem solution {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
    {β α : Type*} [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α] [DecidableEq Ω₂]
    (φ : Ω₁ → α) (Y : Ω₁ → β) :
    mutualInfo (fun x : Ω₁ × Ω₂ => (φ x.1, x.2)) (fun x : Ω₁ × Ω₂ => Y x.1)
      = mutualInfo φ Y := by
  have hN1 : (Fintype.card Ω₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hN2 : (Fintype.card Ω₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have htot : Fintype.card (Ω₁ × Ω₂) = Fintype.card Ω₁ * Fintype.card Ω₂ := Fintype.card_prod _ _
  have halg : ∀ p B m : ℝ,
      (Fintype.card Ω₂ : ℝ) * ((1 / (Fintype.card Ω₂ : ℝ)) * p + B * m)
        = p + B * ((Fintype.card Ω₂ : ℝ) * m) := by
    intro p B m
    field_simp
  -- ===== fibre counts =====
  have cX : ∀ (a : α) (w : Ω₂),
      (fiber (fun x : Ω₁ × Ω₂ => (φ x.1, x.2)) (a, w)).card = (fiber φ a).card := by
    intro a w
    have hstep : ∀ u : Ω₁, (∑ v : Ω₂, if (φ u, v) = (a, w) then (1 : ℕ) else 0)
        = if φ u = a then 1 else 0 := by
      intro u
      have hiff : ∀ v : Ω₂, ((φ u, v) = (a, w)) ↔ (φ u = a ∧ v = w) := by
        intro v
        rw [Prod.mk.injEq]
      simp only [hiff]
      by_cases h : φ u = a
      · simp [h]
      · simp [h]
    simp only [fiber, Finset.card_filter, Fintype.sum_prod_type]
    simp only [hstep]
  have cY : ∀ b : β, (fiber (fun x : Ω₁ × Ω₂ => Y x.1) b).card
      = (fiber Y b).card * Fintype.card Ω₂ := by
    intro b
    have hstep : ∀ u : Ω₁, (∑ _v : Ω₂, if Y u = b then (1 : ℕ) else 0)
        = (if Y u = b then (1 : ℕ) else 0) * Fintype.card Ω₂ := by
      intro u
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    simp only [fiber, Finset.card_filter, Fintype.sum_prod_type]
    simp only [hstep]
    rw [← Finset.sum_mul]
  have cJ : ∀ (a : α) (w : Ω₂) (b : β),
      (fiber (joint (fun x : Ω₁ × Ω₂ => (φ x.1, x.2)) (fun x : Ω₁ × Ω₂ => Y x.1))
        ((a, w), b)).card = (fiber (joint φ Y) (a, b)).card := by
    intro a w b
    have hstep : ∀ u : Ω₁,
        (∑ v : Ω₂, if ((φ u, v), Y u) = ((a, w), b) then (1 : ℕ) else 0)
          = if (φ u, Y u) = (a, b) then 1 else 0 := by
      intro u
      have hiff : ∀ v : Ω₂, (((φ u, v), Y u) = ((a, w), b)) ↔ ((φ u, Y u) = (a, b) ∧ v = w) := by
        intro v
        simp only [Prod.mk.injEq]
        constructor
        · intro h; exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩
        · intro h; exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩
      simp only [hiff]
      by_cases h : (φ u, Y u) = (a, b)
      · simp [h]
      · simp [h]
    simp only [fiber, joint, Finset.card_filter, Fintype.sum_prod_type]
    simp only [hstep]
  -- ===== probabilities =====
  have hpX : ∀ (a : α) (w : Ω₂),
      prb (fun x : Ω₁ × Ω₂ => (φ x.1, x.2)) (a, w)
        = prb φ a * (1 / (Fintype.card Ω₂ : ℝ)) := by
    intro a w
    simp only [prb, cX a w, htot, Nat.cast_mul]
    rw [div_mul_div_comm, mul_one]
  have hpY : ∀ b : β, prb (fun x : Ω₁ × Ω₂ => Y x.1) b = prb Y b := by
    intro b
    simp only [prb, cY b, htot, Nat.cast_mul]
    rw [div_eq_div_iff (mul_ne_zero hN1 hN2) hN1]
    ring
  have hpJ : ∀ (a : α) (w : Ω₂) (b : β),
      prb (joint (fun x : Ω₁ × Ω₂ => (φ x.1, x.2)) (fun x : Ω₁ × Ω₂ => Y x.1)) ((a, w), b)
        = prb (joint φ Y) (a, b) * (1 / (Fintype.card Ω₂ : ℝ)) := by
    intro a w b
    simp only [prb, cJ a w b, htot, Nat.cast_mul]
    rw [div_mul_div_comm, mul_one]
  -- ===== the marginals sum to one =====
  have hsum1 : ∑ a : α, prb φ a = 1 := by
    simp only [prb, fiber]
    rw [← Finset.sum_div, div_eq_one_iff_eq hN1, ← Nat.cast_sum]
    congr 1
    rw [← Finset.card_univ (α := Ω₁)]
    exact (Finset.card_eq_sum_card_fiberwise
      (fun ω _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
  have hsumJ : (∑ a : α, ∑ b : β, prb (joint φ Y) (a, b)) = 1 := by
    rw [← Fintype.sum_prod_type]
    simp only [prb, fiber]
    rw [← Finset.sum_div, div_eq_one_iff_eq hN1, ← Nat.cast_sum]
    congr 1
    rw [← Finset.card_univ (α := Ω₁)]
    exact (Finset.card_eq_sum_card_fiberwise
      (fun ω _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
  -- ===== the three entropies =====
  have hHX : H (fun x : Ω₁ × Ω₂ => (φ x.1, x.2))
      = H φ + (Fintype.card Ω₂ : ℝ) * negMulLog (1 / (Fintype.card Ω₂ : ℝ)) := by
    have hstep : ∀ (a : α) (w : Ω₂),
        negMulLog (prb (fun x : Ω₁ × Ω₂ => (φ x.1, x.2)) (a, w))
          = (1 / (Fintype.card Ω₂ : ℝ)) * negMulLog (prb φ a)
            + prb φ a * negMulLog (1 / (Fintype.card Ω₂ : ℝ)) := by
      intro a w
      rw [hpX a w]
      exact Real.negMulLog_mul _ _
    have hinner : ∀ a : α,
        (∑ _w : Ω₂, ((1 / (Fintype.card Ω₂ : ℝ)) * negMulLog (prb φ a)
            + prb φ a * negMulLog (1 / (Fintype.card Ω₂ : ℝ))))
          = negMulLog (prb φ a)
            + prb φ a * ((Fintype.card Ω₂ : ℝ) * negMulLog (1 / (Fintype.card Ω₂ : ℝ))) := by
      intro a
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact halg _ _ _
    simp only [H]
    rw [Fintype.sum_prod_type]
    simp only [hstep, hinner]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum1, one_mul]
  have hHY : H (fun x : Ω₁ × Ω₂ => Y x.1) = H Y := by
    simp only [H, hpY]
  have hHJ : H (joint (fun x : Ω₁ × Ω₂ => (φ x.1, x.2)) (fun x : Ω₁ × Ω₂ => Y x.1))
      = H (joint φ Y) + (Fintype.card Ω₂ : ℝ) * negMulLog (1 / (Fintype.card Ω₂ : ℝ)) := by
    have hstep : ∀ (a : α) (w : Ω₂) (b : β),
        negMulLog (prb (joint (fun x : Ω₁ × Ω₂ => (φ x.1, x.2))
            (fun x : Ω₁ × Ω₂ => Y x.1)) ((a, w), b))
          = (1 / (Fintype.card Ω₂ : ℝ)) * negMulLog (prb (joint φ Y) (a, b))
            + prb (joint φ Y) (a, b) * negMulLog (1 / (Fintype.card Ω₂ : ℝ)) := by
      intro a w b
      rw [hpJ a w b]
      exact Real.negMulLog_mul _ _
    have hmid : ∀ a : α,
        (∑ _w : Ω₂, ∑ b : β, ((1 / (Fintype.card Ω₂ : ℝ)) * negMulLog (prb (joint φ Y) (a, b))
            + prb (joint φ Y) (a, b) * negMulLog (1 / (Fintype.card Ω₂ : ℝ))))
          = (∑ b : β, negMulLog (prb (joint φ Y) (a, b)))
            + (∑ b : β, prb (joint φ Y) (a, b))
              * ((Fintype.card Ω₂ : ℝ) * negMulLog (1 / (Fintype.card Ω₂ : ℝ))) := by
      intro a
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      exact halg _ _ _
    simp only [H]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [hstep, hmid]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsumJ, one_mul]
  simp only [mutualInfo, hHX, hHY, hHJ]
  ring
