-- Prove2me | solution 1 for DiophantineLattice.posDef_congr
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:18:54.325442+00:00
-- url     : https://prove2.me/submissions/e092a6ef-f7e8-4223-aee3-a98f0d5dff69

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeCharacteristic
open DiophantineLattice Finset Matrix in
theorem solution {n : ℕ} {U V : Matrix (Fin n) (Fin n) ℤ} (hUV : U * V = 1) (hVU : V * U = 1)
    (B : Matrix (Fin n) (Fin n) ℚ) :
    DiophantineLattice.PosDef ((toRat U)ᵀ * B * (toRat U)) ↔ DiophantineLattice.PosDef B := by
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
  have hUVQ : toRat U * toRat V = 1 := by rw [← htoRat_mul, hUV, htoRat_one]
  have hVUQ : toRat V * toRat U = 1 := by rw [← htoRat_mul, hVU, htoRat_one]
  constructor
  · intro hpd y hy
    have hx : toRat V *ᵥ y ≠ 0 := by
      intro h0
      apply hy
      have e : toRat U *ᵥ (toRat V *ᵥ y) = y := by
        rw [Matrix.mulVec_mulVec, hUVQ, Matrix.one_mulVec]
      rw [h0, Matrix.mulVec_zero] at e
      exact e.symm
    have hlt := hpd _ hx
    rw [hcongr, Matrix.mulVec_mulVec, hUVQ, Matrix.one_mulVec] at hlt
    exact hlt
  · intro hpd x hx
    rw [hcongr]
    refine hpd _ ?_
    intro h0
    apply hx
    have e : toRat V *ᵥ (toRat U *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hVUQ, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at e
    exact e.symm
