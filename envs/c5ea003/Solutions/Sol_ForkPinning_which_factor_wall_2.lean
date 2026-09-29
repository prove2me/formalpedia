-- Prove2me | solution 2 for ForkPinning.which_factor_wall
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:38:00.468799+00:00
-- url     : https://prove2.me/submissions/6dcf9b5c-472c-4267-b40a-4f9ba5034eb6

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
import Definitions.Def_Probability_ForkPinningSemiprime
open ForkPinning Finset Real in
theorem solution : mutualInfo cubicClassOfN firstFactorSplits = 0 := by
  have hMn : Fintype.card (ZMod 3) ≠ 0 := Fintype.card_ne_zero
  have hM : (Fintype.card (ZMod 3) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hMn
  -- the abstract algebra: a uniform first statistic with a product joint law has zero information
  have main : ∀ (n : ℕ) (c : Bool → ℕ), (n : ℝ) ≠ 0 → (∑ b : Bool, c b) = n →
      ∀ (pX : ZMod 3 → ℝ) (pY : Bool → ℝ) (pJ : ZMod 3 × Bool → ℝ),
      (∀ g : ZMod 3, pX g = 1 / (Fintype.card (ZMod 3) : ℝ)) →
      (∀ b : Bool, pY b = (c b : ℝ) / (n : ℝ)) →
      (∀ (g : ZMod 3) (b : Bool),
        pJ (g, b) = (1 / (Fintype.card (ZMod 3) : ℝ)) * ((c b : ℝ) / (n : ℝ))) →
      (∑ g : ZMod 3, negMulLog (pX g)) + (∑ b : Bool, negMulLog (pY b))
        - (∑ p : ZMod 3 × Bool, negMulLog (pJ p)) = 0 := by
    intro n c hnR hsum pX pY pJ hX hY hJ
    have hq1 : ∑ b : Bool, ((c b : ℝ) / (n : ℝ)) = 1 := by
      rw [← Finset.sum_div, ← Nat.cast_sum, hsum, div_self hnR]
    have hXsum : (∑ g : ZMod 3, negMulLog (pX g))
        = (Fintype.card (ZMod 3) : ℝ) * negMulLog (1 / (Fintype.card (ZMod 3) : ℝ)) := by
      simp only [hX]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hYsum : (∑ b : Bool, negMulLog (pY b))
        = ∑ b : Bool, negMulLog ((c b : ℝ) / (n : ℝ)) := by
      simp only [hY]
    have hinner : ∀ g : ZMod 3, (∑ b : Bool, negMulLog (pJ (g, b)))
        = negMulLog (1 / (Fintype.card (ZMod 3) : ℝ))
          + (1 / (Fintype.card (ZMod 3) : ℝ))
            * ∑ b : Bool, negMulLog ((c b : ℝ) / (n : ℝ)) := by
      intro g
      have hstep : ∀ b : Bool, negMulLog (pJ (g, b))
          = ((c b : ℝ) / (n : ℝ)) * negMulLog (1 / (Fintype.card (ZMod 3) : ℝ))
            + (1 / (Fintype.card (ZMod 3) : ℝ)) * negMulLog ((c b : ℝ) / (n : ℝ)) := by
        intro b
        rw [hJ g b]
        exact Real.negMulLog_mul _ _
      simp only [hstep]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq1, one_mul]
    have hJsum : (∑ p : ZMod 3 × Bool, negMulLog (pJ p))
        = (Fintype.card (ZMod 3) : ℝ) * negMulLog (1 / (Fintype.card (ZMod 3) : ℝ))
          + (Fintype.card (ZMod 3) : ℝ)
            * ((1 / (Fintype.card (ZMod 3) : ℝ))
              * ∑ b : Bool, negMulLog ((c b : ℝ) / (n : ℝ))) := by
      rw [Fintype.sum_prod_type]
      simp only [hinner]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcan : (Fintype.card (ZMod 3) : ℝ)
        * ((1 / (Fintype.card (ZMod 3) : ℝ)) * ∑ b : Bool, negMulLog ((c b : ℝ) / (n : ℝ)))
        = ∑ b : Bool, negMulLog ((c b : ℝ) / (n : ℝ)) := by
      rw [← mul_assoc, mul_one_div, div_self hM, one_mul]
    rw [hXsum, hYsum, hJsum, hcan]
    ring
  have htot : Fintype.card (ZMod 3 × ZMod 3)
      = Fintype.card (ZMod 3) * Fintype.card (ZMod 3) := Fintype.card_prod _ _
  have hcsum : (∑ b : Bool, (univ.filter (fun a : ZMod 3 => decide (a = 0) = b)).card)
      = Fintype.card (ZMod 3) := by
    rw [← Finset.card_univ (α := ZMod 3)]
    exact (Finset.card_eq_sum_card_fiberwise
      (fun a _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
  -- fibre counts: the free second factor makes the class of the product uniform
  have cA : ∀ g : ZMod 3, (fiber cubicClassOfN g).card = Fintype.card (ZMod 3) := by
    intro g
    have hstep : ∀ a : ZMod 3, (∑ w : ZMod 3, if a + w = g then (1 : ℕ) else 0) = 1 := by
      intro a
      have hiff : ∀ w : ZMod 3, (a + w = g) ↔ (w = g - a) := by
        intro w
        constructor
        · intro hw; rw [← hw]; ring
        · intro hw; rw [hw]; ring
      simp only [hiff]
      simp
    simp only [fiber, cubicClassOfN, Finset.card_filter, Fintype.sum_prod_type]
    simp only [hstep]
    simp
  have cB : ∀ b : Bool, (fiber firstFactorSplits b).card
      = (univ.filter (fun a : ZMod 3 => decide (a = 0) = b)).card * Fintype.card (ZMod 3) := by
    intro b
    have hstep : ∀ a : ZMod 3, (∑ _w : ZMod 3, if decide (a = 0) = b then (1 : ℕ) else 0)
        = (if decide (a = 0) = b then (1 : ℕ) else 0) * Fintype.card (ZMod 3) := by
      intro a
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    simp only [fiber, firstFactorSplits, Finset.card_filter, Fintype.sum_prod_type]
    simp only [hstep]
    rw [← Finset.sum_mul, ← Finset.card_filter]
  have cC : ∀ (g : ZMod 3) (b : Bool),
      (fiber (joint cubicClassOfN firstFactorSplits) (g, b)).card
        = (univ.filter (fun a : ZMod 3 => decide (a = 0) = b)).card := by
    intro g b
    have hstep : ∀ a : ZMod 3,
        (∑ w : ZMod 3, if (a + w, decide (a = 0)) = (g, b) then (1 : ℕ) else 0)
          = (if decide (a = 0) = b then (1 : ℕ) else 0) := by
      intro a
      have hiff : ∀ w : ZMod 3,
          ((a + w, decide (a = 0)) = (g, b)) ↔ (w = g - a ∧ decide (a = 0) = b) := by
        intro w
        rw [Prod.mk.injEq]
        constructor
        · intro hh; exact ⟨by rw [← hh.1]; ring, hh.2⟩
        · intro hh; exact ⟨by rw [hh.1]; ring, hh.2⟩
      simp only [hiff]
      by_cases hb : decide (a = 0) = b
      · simp [hb]
      · simp [hb]
    simp only [fiber, joint, cubicClassOfN, firstFactorSplits, Finset.card_filter,
      Fintype.sum_prod_type]
    simp only [hstep]
  -- probabilities
  have hpX : ∀ g : ZMod 3, prb cubicClassOfN g = 1 / (Fintype.card (ZMod 3) : ℝ) := by
    intro g
    simp only [prb]
    rw [cA g, htot, Nat.cast_mul, div_eq_div_iff (mul_ne_zero hM hM) hM]
    ring
  have hpY : ∀ b : Bool, prb firstFactorSplits b
      = ((univ.filter (fun a : ZMod 3 => decide (a = 0) = b)).card : ℝ)
        / (Fintype.card (ZMod 3) : ℝ) := by
    intro b
    simp only [prb]
    rw [cB b, htot, Nat.cast_mul, Nat.cast_mul, div_eq_div_iff (mul_ne_zero hM hM) hM]
    ring
  have hpJ : ∀ (g : ZMod 3) (b : Bool),
      prb (joint cubicClassOfN firstFactorSplits) (g, b)
      = (1 / (Fintype.card (ZMod 3) : ℝ))
        * (((univ.filter (fun a : ZMod 3 => decide (a = 0) = b)).card : ℝ)
            / (Fintype.card (ZMod 3) : ℝ)) := by
    intro g b
    simp only [prb]
    rw [cC g b, htot, Nat.cast_mul, div_mul_div_comm, one_mul,
      div_eq_div_iff (mul_ne_zero hM hM) (mul_ne_zero hM hM)]
  simp only [mutualInfo, H]
  exact main (Fintype.card (ZMod 3))
    (fun b => (univ.filter (fun a : ZMod 3 => decide (a = 0) = b)).card)
    hM hcsum _ _ _ hpX hpY hpJ
