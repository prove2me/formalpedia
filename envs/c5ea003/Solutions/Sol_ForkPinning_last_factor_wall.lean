-- Prove2me | solution 1 for ForkPinning.last_factor_wall
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:32:53.639558+00:00
-- url     : https://prove2.me/submissions/38606441-c2a5-4ee5-923a-d7921f5f4d83

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningKFactors
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {β : Type*} [Fintype β] [DecidableEq β] (h : Ω → G) (F : Ω → β) :
    mutualInfo (fun x : Ω × G => h x.1 * x.2) (fun x : Ω × G => F x.1) = 0 := by
  have hMn : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hNn : Fintype.card Ω ≠ 0 := Fintype.card_ne_zero
  have hM : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hMn
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNn
  -- the abstract algebra: a uniform first statistic with a product joint law has zero information
  have main : ∀ (n : ℕ) (c : β → ℕ), (n : ℝ) ≠ 0 → (∑ b : β, c b) = n →
      ∀ (pX : G → ℝ) (pY : β → ℝ) (pJ : G × β → ℝ),
      (∀ g : G, pX g = 1 / (Fintype.card G : ℝ)) →
      (∀ b : β, pY b = (c b : ℝ) / (n : ℝ)) →
      (∀ (g : G) (b : β), pJ (g, b) = (1 / (Fintype.card G : ℝ)) * ((c b : ℝ) / (n : ℝ))) →
      (∑ g : G, negMulLog (pX g)) + (∑ b : β, negMulLog (pY b))
        - (∑ p : G × β, negMulLog (pJ p)) = 0 := by
    intro n c hnR hsum pX pY pJ hX hY hJ
    have hq1 : ∑ b : β, ((c b : ℝ) / (n : ℝ)) = 1 := by
      rw [← Finset.sum_div, ← Nat.cast_sum, hsum, div_self hnR]
    have hXsum : (∑ g : G, negMulLog (pX g))
        = (Fintype.card G : ℝ) * negMulLog (1 / (Fintype.card G : ℝ)) := by
      simp only [hX]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hYsum : (∑ b : β, negMulLog (pY b))
        = ∑ b : β, negMulLog ((c b : ℝ) / (n : ℝ)) := by
      simp only [hY]
    have hinner : ∀ g : G, (∑ b : β, negMulLog (pJ (g, b)))
        = negMulLog (1 / (Fintype.card G : ℝ))
          + (1 / (Fintype.card G : ℝ)) * ∑ b : β, negMulLog ((c b : ℝ) / (n : ℝ)) := by
      intro g
      have hstep : ∀ b : β, negMulLog (pJ (g, b))
          = ((c b : ℝ) / (n : ℝ)) * negMulLog (1 / (Fintype.card G : ℝ))
            + (1 / (Fintype.card G : ℝ)) * negMulLog ((c b : ℝ) / (n : ℝ)) := by
        intro b
        rw [hJ g b]
        exact Real.negMulLog_mul _ _
      simp only [hstep]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq1, one_mul]
    have hJsum : (∑ p : G × β, negMulLog (pJ p))
        = (Fintype.card G : ℝ) * negMulLog (1 / (Fintype.card G : ℝ))
          + (Fintype.card G : ℝ)
            * ((1 / (Fintype.card G : ℝ)) * ∑ b : β, negMulLog ((c b : ℝ) / (n : ℝ))) := by
      rw [Fintype.sum_prod_type]
      simp only [hinner]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcan : (Fintype.card G : ℝ)
        * ((1 / (Fintype.card G : ℝ)) * ∑ b : β, negMulLog ((c b : ℝ) / (n : ℝ)))
        = ∑ b : β, negMulLog ((c b : ℝ) / (n : ℝ)) := by
      rw [← mul_assoc, mul_one_div, div_self hM, one_mul]
    rw [hXsum, hYsum, hJsum, hcan]
    ring
  have htot : Fintype.card (Ω × G) = Fintype.card Ω * Fintype.card G := Fintype.card_prod Ω G
  have hcsum : (∑ b : β, (univ.filter (fun ω : Ω => F ω = b)).card) = Fintype.card Ω := by
    rw [← Finset.card_univ (α := Ω)]
    exact (Finset.card_eq_sum_card_fiberwise (fun u _ => by simp)).symm
  -- fibre counts: the free group coordinate makes the first statistic uniform
  have cA : ∀ g : G, (fiber (fun x : Ω × G => h x.1 * x.2) g).card = Fintype.card Ω := by
    intro g
    have hstep : ∀ ω : Ω, (∑ w : G, if h ω * w = g then (1 : ℕ) else 0) = 1 := by
      intro ω
      have hiff : ∀ w : G, (h ω * w = g) ↔ (w = (h ω)⁻¹ * g) := by
        intro w
        constructor
        · intro hw; rw [← hw]; group
        · intro hw; rw [hw]; group
      simp only [hiff]
      simp
    simp only [fiber, Finset.card_filter, Fintype.sum_prod_type]
    simp only [hstep]
    simp
  have cB : ∀ b : β, (fiber (fun x : Ω × G => F x.1) b).card
      = (univ.filter (fun ω : Ω => F ω = b)).card * Fintype.card G := by
    intro b
    have hstep : ∀ ω : Ω, (∑ _w : G, if F ω = b then (1 : ℕ) else 0)
        = (if F ω = b then (1 : ℕ) else 0) * Fintype.card G := by
      intro ω
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    simp only [fiber, Finset.card_filter, Fintype.sum_prod_type]
    simp only [hstep]
    rw [← Finset.sum_mul, ← Finset.card_filter]
  have cC : ∀ (g : G) (b : β),
      (fiber (joint (fun x : Ω × G => h x.1 * x.2) (fun x : Ω × G => F x.1)) (g, b)).card
        = (univ.filter (fun ω : Ω => F ω = b)).card := by
    intro g b
    have hstep : ∀ ω : Ω,
        (∑ w : G, if (h ω * w, F ω) = (g, b) then (1 : ℕ) else 0)
          = (if F ω = b then (1 : ℕ) else 0) := by
      intro ω
      have hiff : ∀ w : G, ((h ω * w, F ω) = (g, b)) ↔ (w = (h ω)⁻¹ * g ∧ F ω = b) := by
        intro w
        rw [Prod.mk.injEq]
        constructor
        · intro hh; exact ⟨by rw [← hh.1]; group, hh.2⟩
        · intro hh; exact ⟨by rw [hh.1]; group, hh.2⟩
      simp only [hiff]
      by_cases hb : F ω = b
      · simp [hb]
      · simp [hb]
    simp only [fiber, joint, Finset.card_filter, Fintype.sum_prod_type]
    simp only [hstep]
  -- probabilities
  have hpX : ∀ g : G, prb (fun x : Ω × G => h x.1 * x.2) g = 1 / (Fintype.card G : ℝ) := by
    intro g
    simp only [prb]
    rw [cA g, htot, Nat.cast_mul, div_eq_div_iff (mul_ne_zero hN hM) hM]
    ring
  have hpY : ∀ b : β, prb (fun x : Ω × G => F x.1) b
      = ((univ.filter (fun ω : Ω => F ω = b)).card : ℝ) / (Fintype.card Ω : ℝ) := by
    intro b
    simp only [prb]
    rw [cB b, htot, Nat.cast_mul, Nat.cast_mul, div_eq_div_iff (mul_ne_zero hN hM) hN]
    ring
  have hpJ : ∀ (g : G) (b : β),
      prb (joint (fun x : Ω × G => h x.1 * x.2) (fun x : Ω × G => F x.1)) (g, b)
      = (1 / (Fintype.card G : ℝ))
        * (((univ.filter (fun ω : Ω => F ω = b)).card : ℝ) / (Fintype.card Ω : ℝ)) := by
    intro g b
    simp only [prb]
    rw [cC g b, htot, Nat.cast_mul, div_mul_div_comm, one_mul,
      div_eq_div_iff (mul_ne_zero hN hM) (mul_ne_zero hM hN)]
    ring
  simp only [mutualInfo, H]
  exact main (Fintype.card Ω) (fun b => (univ.filter (fun ω : Ω => F ω = b)).card)
    hN hcsum _ _ _ hpX hpY hpJ
