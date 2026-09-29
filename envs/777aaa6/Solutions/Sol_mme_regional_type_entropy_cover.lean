-- Prove2me | solution 1 for mme_regional_type_entropy_cover
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:16:31.821244+00:00
-- url     : https://prove2.me/submissions/c1bd5a63-04ec-42d3-8107-dd2e7b785a63

import Theorems.Thm_mme_regional_prescribed_profile_card
import Theorems.Thm_mme_regional_dependent_profile_entropy_bounds
import Mathlib
open BigOperators MME.RecursiveThinSplit MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000

private theorem count_sum {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ} (w : Fin n → A) :
    ∑ a, count w a = n := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv w)
  simpa only [Fintype.card_sigma,Fintype.card_subtype,Fintype.card_fin,count] using h

theorem solution {R : Type*} [Fintype R] {A : R → Type*} [∀ r, Fintype (A r)]
    (n : R → ℕ) (S : ℕ) (hn : ∀ r, n r ≤ S)
    (F : Finset (∀ r, Fin (n r) → A r)) (B : ℝ)
    (hB : ∀ w ∈ F, (∑ r, massEntropy (fun c ↦ (count (w r) c : ℝ))) ≤ B) :
    (F.card : ℝ) ≤ ((S : ℝ) + 1) ^ (∑ r, Fintype.card (A r)) * Real.exp B := by
  classical
  let Code := ∀ r, A r → Fin (S + 1)
  let code : (∀ r, Fin (n r) → A r) → Code := fun w r c ↦
    ⟨count (w r) c,by
      have hc : count (w r) c ≤ n r := by
        exact (Finset.card_filter_le _ _).trans (by simp)
      exact Nat.lt_succ_of_le (hc.trans (hn r))⟩
  have hcard (w : ∀ r, Fin (n r) → A r) :
      ((Finset.univ.filter (fun v : ∀ r, Fin (n r) → A r ↦
        ∀ r c, count (v r) c = count (w r) c)).card : ℝ) ≤
      Real.exp (∑ r, massEntropy (fun c ↦ (count (w r) c : ℝ))) := by
    have hc := mme_regional_prescribed_profile_card n (fun r c ↦ count (w r) c)
      (fun r ↦ count_sum (w r))
    simp only [Fintype.card_subtype] at hc
    rw [hc]
    have he := (mme_regional_dependent_profile_entropy_bounds (fun r c ↦ count (w r) c) S
      (fun r ↦ (count_sum (w r)).le.trans (hn r))).1
    simpa only [count_sum,Nat.cast_prod] using he
  have hf (y : Code) (hy : y ∈ F.image code) :
      ((F.filter (fun w ↦ code w = y)).card : ℝ) ≤ Real.exp B := by
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hsub : F.filter (fun v ↦ code v = code w) ⊆
        Finset.univ.filter (fun v : ∀ r, Fin (n r) → A r ↦
          ∀ r c, count (v r) c = count (w r) c) := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun r c ↦ ?_⟩
      have hh := congrFun (congrFun (Finset.mem_filter.mp hv).2 r) c
      exact congrArg Fin.val hh
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((hcard w).trans (Real.exp_le_exp.mpr (hB w hw)))
  have hcount : ∑ y ∈ F.image code, (F.filter (fun w ↦ code w = y)).card = F.card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter F (F.image code) code
    rw [show F.filter (fun w ↦ code w ∈ F.image code) = F by
      ext w
      simp only [Finset.mem_filter,and_iff_left_iff_imp]
      exact fun hw ↦ Finset.mem_image_of_mem _ hw] at h
    exact h
  calc
    (F.card : ℝ) = ∑ y ∈ F.image code, ((F.filter (fun w ↦ code w = y)).card : ℝ) := by
      exact_mod_cast hcount.symm
    _ ≤ ∑ _y ∈ F.image code, Real.exp B := Finset.sum_le_sum hf
    _ = ((F.image code).card : ℝ) * Real.exp B := by simp
    _ ≤ (Fintype.card Code : ℝ) * Real.exp B :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ _)) (Real.exp_pos _).le
    _ = _ := by
      simp only [Code,Fintype.card_pi,Fintype.card_fun,Fintype.card_fin,Nat.cast_prod,Nat.cast_pow,
        Nat.cast_add,Nat.cast_one,Finset.prod_const,Finset.card_univ,Finset.prod_pow_eq_pow_sum]
