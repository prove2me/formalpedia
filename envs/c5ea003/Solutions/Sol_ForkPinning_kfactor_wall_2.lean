-- Prove2me | solution 2 for ForkPinning.kfactor_wall
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:28:00.119675+00:00
-- url     : https://prove2.me/submissions/eaf52ad3-3312-4ec3-a61e-a12c61b2615c

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningKFactors
open ForkPinning Finset Real in
theorem solution {G : Type*} [Group G] [Fintype G] [Nonempty G] [DecidableEq G]
    {β : Type*} [Fintype β] [DecidableEq β] {k : ℕ} (F : (Fin k → G) → β) :
    mutualInfo (fun v : Fin (k + 1) → G => vecProd v)
      (fun v : Fin (k + 1) → G => F (fun i => v i.castSucc)) = 0 := by
  have hMn : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hNn : Fintype.card (Fin k → G) ≠ 0 := Fintype.card_ne_zero
  have hM : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hMn
  have hN : (Fintype.card (Fin k → G) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNn
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
  -- the product of a snoc'd vector splits off its last entry
  have hvp : ∀ (u : Fin k → G) (w : G), vecProd ((snocEquiv k G) (u, w)) = vecProd u * w := by
    intro u w
    have he : (snocEquiv k G) (u, w) = Fin.snoc u w := rfl
    have h1 : (fun i : Fin k => (Fin.snoc u w : Fin (k + 1) → G) i.castSucc) = u := by
      funext i; simp
    show (List.ofFn ((snocEquiv k G) (u, w))).prod = (List.ofFn u).prod * w
    rw [he, List.ofFn_succ', List.prod_concat, h1, Fin.snoc_last]
  have hinit : ∀ (u : Fin k → G) (w : G),
      (fun i : Fin k => ((snocEquiv k G) (u, w)) i.castSucc) = u := by
    intro u w; funext i; simp [snocEquiv]
  have htot : Fintype.card (Fin (k + 1) → G)
      = Fintype.card (Fin k → G) * Fintype.card G := by
    simp [Fintype.card_fun, pow_succ]
  have hcsum : (∑ b : β, (univ.filter (fun u : Fin k → G => F u = b)).card)
      = Fintype.card (Fin k → G) := by
    rw [← Finset.card_univ (α := Fin k → G)]
    exact (Finset.card_eq_sum_card_fiberwise (fun u _ => by simp)).symm
  -- fibre counts
  have cA : ∀ g : G, (fiber (fun v : Fin (k + 1) → G => vecProd v) g).card
      = Fintype.card (Fin k → G) := by
    intro g
    have hre : (∑ v : Fin (k + 1) → G, (if vecProd v = g then (1 : ℕ) else 0))
        = ∑ x : (Fin k → G) × G, (if vecProd ((snocEquiv k G) x) = g then (1 : ℕ) else 0) :=
      (Equiv.sum_comp (snocEquiv k G) (fun v => if vecProd v = g then (1 : ℕ) else 0)).symm
    have hstep : ∀ u : Fin k → G,
        (∑ w : G, if vecProd ((snocEquiv k G) (u, w)) = g then (1 : ℕ) else 0) = 1 := by
      intro u
      have hiff : ∀ w : G, (vecProd ((snocEquiv k G) (u, w)) = g) ↔ (w = (vecProd u)⁻¹ * g) := by
        intro w
        rw [hvp u w]
        constructor
        · intro hw; rw [← hw]; group
        · intro hw; rw [hw]; group
      simp only [hiff]
      simp
    simp only [fiber]
    rw [Finset.card_filter, hre, Fintype.sum_prod_type]
    simp only [hstep]
    simp
  have cB : ∀ b : β,
      (fiber (fun v : Fin (k + 1) → G => F (fun i => v i.castSucc)) b).card
        = (univ.filter (fun u : Fin k → G => F u = b)).card * Fintype.card G := by
    intro b
    have hre : (∑ v : Fin (k + 1) → G, (if F (fun i => v i.castSucc) = b then (1 : ℕ) else 0))
        = ∑ x : (Fin k → G) × G,
            (if F (fun i => ((snocEquiv k G) x) i.castSucc) = b then (1 : ℕ) else 0) :=
      (Equiv.sum_comp (snocEquiv k G)
        (fun v => if F (fun i => v i.castSucc) = b then (1 : ℕ) else 0)).symm
    have hstep : ∀ u : Fin k → G,
        (∑ w : G, if F (fun i => ((snocEquiv k G) (u, w)) i.castSucc) = b then (1 : ℕ) else 0)
          = (if F u = b then (1 : ℕ) else 0) * Fintype.card G := by
      intro u
      have hcongr : ∀ w : G,
          (if F (fun i => ((snocEquiv k G) (u, w)) i.castSucc) = b then (1 : ℕ) else 0)
            = (if F u = b then (1 : ℕ) else 0) := by
        intro w; rw [hinit u w]
      rw [Finset.sum_congr rfl (fun w _ => hcongr w), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_comm]
    simp only [fiber]
    rw [Finset.card_filter, hre, Fintype.sum_prod_type]
    simp only [hstep]
    rw [← Finset.sum_mul, ← Finset.card_filter]
  have cC : ∀ (g : G) (b : β),
      (fiber (joint (fun v : Fin (k + 1) → G => vecProd v)
        (fun v : Fin (k + 1) → G => F (fun i => v i.castSucc))) (g, b)).card
        = (univ.filter (fun u : Fin k → G => F u = b)).card := by
    intro g b
    have hre : (∑ v : Fin (k + 1) → G,
          (if (vecProd v, F (fun i => v i.castSucc)) = (g, b) then (1 : ℕ) else 0))
        = ∑ x : (Fin k → G) × G,
            (if (vecProd ((snocEquiv k G) x),
              F (fun i => ((snocEquiv k G) x) i.castSucc)) = (g, b) then (1 : ℕ) else 0) :=
      (Equiv.sum_comp (snocEquiv k G)
        (fun v => if (vecProd v, F (fun i => v i.castSucc)) = (g, b) then (1 : ℕ) else 0)).symm
    have hstep : ∀ u : Fin k → G,
        (∑ w : G, if (vecProd ((snocEquiv k G) (u, w)),
            F (fun i => ((snocEquiv k G) (u, w)) i.castSucc)) = (g, b) then (1 : ℕ) else 0)
          = (if F u = b then (1 : ℕ) else 0) := by
      intro u
      have hiff : ∀ w : G,
          ((vecProd ((snocEquiv k G) (u, w)),
            F (fun i => ((snocEquiv k G) (u, w)) i.castSucc)) = (g, b))
            ↔ (w = (vecProd u)⁻¹ * g ∧ F u = b) := by
        intro w
        rw [Prod.mk.injEq, hvp u w, hinit u w]
        constructor
        · intro h; exact ⟨by rw [← h.1]; group, h.2⟩
        · intro h; exact ⟨by rw [h.1]; group, h.2⟩
      simp only [hiff]
      by_cases hb : F u = b
      · simp [hb]
      · simp [hb]
    simp only [fiber, joint]
    rw [Finset.card_filter, hre, Fintype.sum_prod_type]
    simp only [hstep]
    rw [← Finset.card_filter]
  -- probabilities
  have hpX : ∀ g : G, prb (fun v : Fin (k + 1) → G => vecProd v) g
      = 1 / (Fintype.card G : ℝ) := by
    intro g
    simp only [prb]
    rw [cA g, htot, Nat.cast_mul, div_eq_div_iff (mul_ne_zero hN hM) hM]
    ring
  have hpY : ∀ b : β, prb (fun v : Fin (k + 1) → G => F (fun i => v i.castSucc)) b
      = ((univ.filter (fun u : Fin k → G => F u = b)).card : ℝ)
        / (Fintype.card (Fin k → G) : ℝ) := by
    intro b
    simp only [prb]
    rw [cB b, htot, Nat.cast_mul, Nat.cast_mul, div_eq_div_iff (mul_ne_zero hN hM) hN]
    ring
  have hpJ : ∀ (g : G) (b : β),
      prb (joint (fun v : Fin (k + 1) → G => vecProd v)
        (fun v : Fin (k + 1) → G => F (fun i => v i.castSucc))) (g, b)
      = (1 / (Fintype.card G : ℝ))
        * (((univ.filter (fun u : Fin k → G => F u = b)).card : ℝ)
            / (Fintype.card (Fin k → G) : ℝ)) := by
    intro g b
    simp only [prb]
    rw [cC g b, htot, Nat.cast_mul, div_mul_div_comm, one_mul,
      div_eq_div_iff (mul_ne_zero hN hM) (mul_ne_zero hM hN)]
    ring
  simp only [mutualInfo, H]
  exact main (Fintype.card (Fin k → G))
    (fun b => (univ.filter (fun u : Fin k → G => F u = b)).card) hN hcsum _ _ _ hpX hpY hpJ
