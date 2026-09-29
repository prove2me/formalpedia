-- Prove2me | solution 1 for mme_dwz_same_affine_bucket_conditioned_XZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:29:22.074457+00:00
-- url     : https://prove2.me/submissions/49e181c7-93c3-4b9e-8c03-92f6357fa74c

import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label

open BigOperators
open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p n : ℕ} (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (levelSum : ZMod p)
    (I J K I' J' : Fin (n + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    (hsupport' : ∀ t, I' t + J' t + K t = levelSum)
    (q : (Fin (n + 2) → ZMod p) × ZMod p)
    (hcentral :
      let castS : Finset (ZMod p) :=
        S.image (fun a : ℕ ↦ (a : ZMod p))
      let ω := dwzAsymmetricHashStateOfAffine q
      dwzAsymmetricHashX ω I ∈ castS ∧
        dwzAsymmetricHashY ω J ∈ castS ∧
        dwzAsymmetricHashZ levelSum ω K ∈ castS)
    (hcandidate :
      let castS : Finset (ZMod p) :=
        S.image (fun a : ℕ ↦ (a : ZMod p))
      let ω := dwzAsymmetricHashStateOfAffine q
      dwzAsymmetricHashX ω I' ∈ castS ∧
        dwzAsymmetricHashY ω J' ∈ castS ∧
        dwzAsymmetricHashZ levelSum ω K ∈ castS) :
    let weight : Fin (n + 1) → ZMod p := fun t ↦ q.1 t.castSucc
    let b0 : ZMod p := q.1 (Fin.last (n + 1))
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → ZMod p) → ZMod p := fun w A ↦
      b0 + ∑ t, A t * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → ZMod p) → ZMod p := fun w0 w C ↦
      b0 + (2 : ZMod p)⁻¹ *
        (w0 + ∑ t, (levelSum - C t) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p := fun w ↦
      2 * (∑ t, I t * w t) -
        ∑ t, (levelSum - K t) * w t
    hX weight I' = hZ (conditionedW0 weight) weight K := by
  classical
  dsimp only at hcentral hcandidate ⊢
  let castS : Finset (ZMod p) :=
    S.image (fun a : ℕ ↦ (a : ZMod p))
  have hcentralRetained :
      dwzAsymmetricAffineRetains levelSum castS I J K q :=
    (mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
      hpodd S hSrange hSfree levelSum I J K hsupport q).mp hcentral
  have hcandidateRetained :
      dwzAsymmetricAffineRetains levelSum castS I' J' K q :=
    (mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
      hpodd S hSrange hSfree levelSum I' J' K hsupport' q).mp hcandidate
  obtain ⟨s, hs, hXcentral, _, hZcentral⟩ := hcentralRetained
  obtain ⟨s', hs', hXcandidate, _, hZcandidate⟩ := hcandidateRetained
  have hcentralEq :
      q.1 (Fin.last (n + 1)) + ∑ t, I t * q.1 t.castSucc =
        q.1 (Fin.last (n + 1)) + (2 : ZMod p)⁻¹ *
          (q.2 + ∑ t, (levelSum - K t) * q.1 t.castSucc) := by
    have h := hXcentral.trans hZcentral.symm
    simpa only [dwzAsymmetricHashX, dwzAsymmetricHashZ,
      dwzAsymmetricHashStateOfAffine] using h
  have hcandidateEq :
      q.1 (Fin.last (n + 1)) + ∑ t, I' t * q.1 t.castSucc =
        q.1 (Fin.last (n + 1)) + (2 : ZMod p)⁻¹ *
          (q.2 + ∑ t, (levelSum - K t) * q.1 t.castSucc) := by
    have h := hXcandidate.trans hZcandidate.symm
    simpa only [dwzAsymmetricHashX, dwzAsymmetricHashZ,
      dwzAsymmetricHashStateOfAffine] using h
  have hunit : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hpodd.coprime_two_left
  have hinv : (2 : ZMod p)⁻¹ * 2 = 1 :=
    ZMod.inv_mul_of_unit 2 hunit
  have hconditioned :
      q.1 (Fin.last (n + 1)) + ∑ t, I t * q.1 t.castSucc =
        q.1 (Fin.last (n + 1)) + (2 : ZMod p)⁻¹ *
          ((2 * (∑ t, I t * q.1 t.castSucc) -
              ∑ t, (levelSum - K t) * q.1 t.castSucc) +
            ∑ t, (levelSum - K t) * q.1 t.castSucc) := by
    rw [sub_add_cancel]
    calc
      q.1 (Fin.last (n + 1)) + ∑ t, I t * q.1 t.castSucc =
          q.1 (Fin.last (n + 1)) +
            1 * (∑ t, I t * q.1 t.castSucc) := by ring
      _ = q.1 (Fin.last (n + 1)) +
          ((2 : ZMod p)⁻¹ * 2) *
            (∑ t, I t * q.1 t.castSucc) := by rw [hinv]
      _ = q.1 (Fin.last (n + 1)) + (2 : ZMod p)⁻¹ *
          (2 * (∑ t, I t * q.1 t.castSucc)) := by ring
  exact hcandidateEq.trans (hcentralEq.symm.trans hconditioned)
