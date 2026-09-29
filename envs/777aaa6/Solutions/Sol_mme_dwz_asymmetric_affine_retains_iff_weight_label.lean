-- Prove2me | solution 1 for mme_dwz_asymmetric_affine_retains_iff_weight_label
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:32:41.186632+00:00
-- url     : https://prove2.me/submissions/2bec9d70-1056-4a94-bf12-fff4f642e864

import Definitions.Def_mme_dwz_asymmetric_affine_hash
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_identity

open BigOperators
open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    (q : (Fin (N + 2) → ZMod p) × ZMod p) :
    MME.dwzAsymmetricAffineRetains levelSum S I J K q ↔
      q.1 (Fin.last (N + 1)) +
            ∑ t : Fin (N + 1), I t * q.1 t.castSucc ∈ S ∧
        q.2 =
          (∑ t : Fin (N + 1), I t * q.1 t.castSucc) -
            ∑ t : Fin (N + 1), J t * q.1 t.castSucc := by
  let ω := MME.dwzAsymmetricHashStateOfAffine q
  constructor
  · rintro ⟨s, hsS, hX, hY, _hZ⟩
    have hX' :
        q.1 (Fin.last (N + 1)) +
            ∑ t : Fin (N + 1), I t * q.1 t.castSucc = s := by
      simpa only [MME.dwzAsymmetricHashX,
        MME.dwzAsymmetricHashStateOfAffine] using hX
    have hY' :
        q.1 (Fin.last (N + 1)) + q.2 +
            ∑ t : Fin (N + 1), J t * q.1 t.castSucc = s := by
      simpa only [MME.dwzAsymmetricHashY,
        MME.dwzAsymmetricHashStateOfAffine] using hY
    refine ⟨hX' ▸ hsS, ?_⟩
    apply (eq_sub_iff_add_eq).2
    have heq := hY'.trans hX'.symm
    exact add_left_cancel (a := q.1 (Fin.last (N + 1)))
      (by simpa [add_assoc] using heq)
  · rintro ⟨hlabel, hw0⟩
    let s : ZMod p :=
      q.1 (Fin.last (N + 1)) +
        ∑ t : Fin (N + 1), I t * q.1 t.castSucc
    have hsS : s ∈ S := hlabel
    refine ⟨s, hsS, ?_, ?_, ?_⟩
    · rfl
    · simp only [MME.dwzAsymmetricHashY,
        MME.dwzAsymmetricHashStateOfAffine]
      rw [hw0]
      dsimp only [s]
      abel
    · have hap := mme_dwz_asymmetric_hash_AP_identity
        hpodd levelSum ω I J K hsupport
      have hX : MME.dwzAsymmetricHashX ω I = s := rfl
      have hY : MME.dwzAsymmetricHashY ω J = s := by
        simp only [ω, MME.dwzAsymmetricHashY,
          MME.dwzAsymmetricHashStateOfAffine]
        rw [hw0]
        dsimp only [s]
        abel
      rw [hX, hY] at hap
      have htwo : (2 : ZMod p) ≠ 0 :=
        ((ZMod.isUnit_iff_coprime 2 p).2 hpodd.coprime_two_left).ne_zero
      apply Eq.symm
      apply mul_left_cancel₀ htwo
      simpa [two_mul] using hap
