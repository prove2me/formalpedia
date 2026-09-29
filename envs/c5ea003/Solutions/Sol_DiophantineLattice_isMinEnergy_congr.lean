-- Prove2me | solution 1 for DiophantineLattice.isMinEnergy_congr
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:24:13.142763+00:00
-- url     : https://prove2.me/submissions/c23a729d-cc46-449d-8ec0-4732310315ee

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeCharacteristic
open DiophantineLattice Finset Matrix in
theorem solution {n : ℕ} {U V : Matrix (Fin n) (Fin n) ℤ} (hUV : U * V = 1) (hVU : V * U = 1)
    (B : Matrix (Fin n) (Fin n) ℚ) (lam : ℚ) :
    IsMinEnergy ((toRat U)ᵀ * B * (toRat U)) lam ↔ IsMinEnergy B lam := by
  have hscale : ∀ (B : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (x : Fin n → ℚ),
      form B (fun i => c * x i) = c ^ 2 * form B x := by
    intro B c x
    simp only [form, bil, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hzero : ∀ B : Matrix (Fin n) (Fin n) ℚ, form B (fun _ => (0 : ℚ)) = 0 := by
    intro B
    simp [form, bil]
  have hembz : ∀ m : Fin n → ℤ, emb m = 0 → m = 0 := by
    intro m hm
    funext i
    have := congrFun hm i
    simp only [emb, Pi.zero_apply] at this
    exact_mod_cast this
  have hembne : ∀ {m : Fin n → ℤ}, m ≠ 0 → emb m ≠ 0 := by
    intro m h he
    exact h (hembz m he)
  have hdot : ∀ (B : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ), form B y = y ⬝ᵥ (B *ᵥ y) := by
    intro B y
    simp only [form, bil, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hcongr : ∀ (W B : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ),
      form (Wᵀ * B * W) x = form B (W *ᵥ x) := by
    intro W B x
    rw [hdot, hdot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have htoRat_mul : ∀ (U V : Matrix (Fin n) (Fin n) ℤ), toRat (U * V) = toRat U * toRat V := by
    intro U V
    funext i j
    simp only [toRat, Matrix.map_apply, Matrix.mul_apply]
    push_cast
    rfl
  have htoRat_one : toRat (1 : Matrix (Fin n) (Fin n) ℤ) = 1 := by
    funext i j
    simp only [toRat, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hUemb : ∀ (W : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ),
      toRat W *ᵥ emb m = emb (W *ᵥ m) := by
    intro W m
    funext i
    simp only [toRat, emb, Matrix.mulVec, dotProduct, Matrix.map_apply]
    push_cast
    rfl
  have hne_of_inv : ∀ (W W' : Matrix (Fin n) (Fin n) ℤ), W' * W = 1 → ∀ {m : Fin n → ℤ},
      m ≠ 0 → W *ᵥ m ≠ 0 := by
    intro W W' hinv m hm h0
    apply hm
    have e : W' *ᵥ (W *ᵥ m) = m := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at e
    exact e.symm
  constructor
  · rintro ⟨⟨v, hvne, hvform⟩, hmin⟩
    refine ⟨⟨U *ᵥ v, hne_of_inv U V hVU hvne, ?_⟩, ?_⟩
    · rw [← hUemb, ← hcongr]
      exact hvform
    · intro m hm
      have h1 := hmin _ (hne_of_inv V U hUV hm)
      rw [hcongr, hUemb, Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec] at h1
      exact h1
  · rintro ⟨⟨v, hvne, hvform⟩, hmin⟩
    refine ⟨⟨V *ᵥ v, hne_of_inv V U hUV hvne, ?_⟩, ?_⟩
    · rw [hcongr, hUemb, Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec]
      exact hvform
    · intro m hm
      rw [hcongr, hUemb]
      exact hmin _ (hne_of_inv U V hVU hm)
