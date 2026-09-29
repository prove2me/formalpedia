-- Prove2me | solution 1 for PermutationDichotomy.symmetrize_error
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T16:54:06.64057+00:00
-- url     : https://prove2.me/submissions/6ea5e530-b6b9-4d0d-8fdd-95a6500c8753

import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_PermutationDichotomy

open scoped BigOperators
open Finset ContinuousMap PermutationDichotomy

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {Γ : Type*} [Group Γ] [Fintype Γ]

omit [Fintype ι] [Fintype κ] in
theorem solution (act : Γ →* Equiv.Perm ι) {q : C(Seq ι κ, ℝ)} {g : Seq ι κ → ℝ}
    (hg : InvariantUnder act g) {K : Set (Seq ι κ)} (hKsat : SaturatedUnder act K) {eps : ℝ}
    (hq : ∀ x ∈ K, |q x - g x| < eps) :
    ∀ x ∈ K, |symmetrize act q x - g x| < eps := by
  intro x hx
  classical
  set n : ℝ := (Fintype.card Γ : ℝ)
  have hnpos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hinv : n⁻¹ * n = 1 := inv_mul_cancel₀ hnpos.ne'
  have heval : symmetrize act q x = n⁻¹ * ∑ γ : Γ, q (permAct (act γ) x) := by
    dsimp [symmetrize]
    simp only [ContinuousMap.coe_smul, smul_eq_mul, ContinuousMap.sum_apply, n]
    refine congrArg _ (Fintype.sum_congr _ _ fun γ => ?_)
    change ((compRightAlgHom ℝ ℝ (permCM (act γ))) q) x = q (permAct (act γ) x)
    simp [compRightAlgHom, permCM, ContinuousMap.comp_apply]
  rw [heval]
  have hg_eq : g x = n⁻¹ * (n * g x) := by rw [← mul_assoc, hinv, one_mul]
  rw [hg_eq]
  have hsub :
      n⁻¹ * ∑ γ : Γ, q (permAct (act γ) x) - n⁻¹ * (n * g x) =
        n⁻¹ * ∑ γ : Γ, (q (permAct (act γ) x) - g x) := by
    have hs : ∑ γ : Γ, g x = n * g x := by simp [n, mul_comm]
    rw [← mul_sub, hs.symm, sum_sub_distrib]
  rw [hsub]
  have hterm : ∀ γ : Γ, |q (permAct (act γ) x) - g x| < eps := by
    intro γ
    have hxγ : permAct (act γ) x ∈ K := hKsat γ x hx
    have h1 := hq _ hxγ
    simpa [hg γ x] using h1
  have hnn : 0 ≤ n⁻¹ := inv_nonneg.mpr hnpos.le
  have habs :
      |n⁻¹ * ∑ γ : Γ, (q (permAct (act γ) x) - g x)| ≤
        n⁻¹ * ∑ γ : Γ, |q (permAct (act γ) x) - g x| := by
    have :=
      mul_le_mul_of_nonneg_left
        (abs_sum_le_sum_abs (s := univ) (f := fun γ : Γ => q (permAct (act γ) x) - g x)) hnn
    simpa [abs_mul, abs_of_nonneg hnn] using this
  refine lt_of_le_of_lt habs ?_
  have : Nonempty Γ := Fintype.card_pos_iff.mp (Nat.cast_pos.mp hnpos)
  obtain ⟨γ0⟩ := this
  have hsumlt :
      ∑ γ : Γ, |q (permAct (act γ) x) - g x| < ∑ _γ : Γ, eps :=
    sum_lt_sum (fun γ _ => (hterm γ).le) ⟨γ0, mem_univ _, hterm γ0⟩
  have hmul := mul_lt_mul_of_pos_left hsumlt (inv_pos.mpr hnpos)
  have hsumeps : (∑ _γ : Γ, (eps : ℝ)) = n * eps := by simp [n, mul_comm]
  calc
    n⁻¹ * ∑ γ : Γ, |q (permAct (act γ) x) - g x| < n⁻¹ * ∑ _γ : Γ, eps := hmul
    _ = n⁻¹ * (n * eps) := by rw [hsumeps]
    _ = eps := by rw [← mul_assoc, hinv, one_mul]
