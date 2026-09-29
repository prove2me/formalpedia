-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_retaining_states_weight_filter_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:35:46.619965+00:00
-- url     : https://prove2.me/submissions/f465c795-bb3c-4071-a219-ba2cdbc72ece

import Theorems.Thm_mme_dwz_asymmetric_affine_retains_iff_weight_label

open BigOperators
open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    (W : Finset (Fin (N + 1) → ZMod p)) :
    ((MME.dwzAsymmetricAffineStatesRetaining levelSum S I J K).filter
      (fun q ↦ (fun t ↦ q.1 t.castSucc) ∈ W)).card =
        S.card * W.card := by
  classical
  let Weight := Fin (N + 1) → ZMod p
  let State := (Fin (N + 2) → ZMod p) × ZMod p
  let states : Finset State :=
    (MME.dwzAsymmetricAffineStatesRetaining levelSum S I J K).filter
      (fun q ↦ (fun t ↦ q.1 t.castSucc) ∈ W)
  let toWeight (q : State) : Weight := fun t ↦ q.1 t.castSucc
  let label (q : State) : ZMod p :=
    q.1 (Fin.last (N + 1)) + ∑ t, I t * toWeight q t
  let mkState (s : ZMod p) (w : Weight) : State :=
    (Fin.lastCases (s - ∑ t, I t * w t) w,
      (∑ t, I t * w t) - ∑ t, J t * w t)
  have hmkWeight (s : ZMod p) (w : Weight) :
      toWeight (mkState s w) = w := by
    funext t
    simp only [toWeight, mkState, Fin.lastCases_castSucc]
  have hmkLabel (s : ZMod p) (w : Weight) :
      label (mkState s w) = s := by
    simp only [label, toWeight, mkState, Fin.lastCases_last,
      Fin.lastCases_castSucc]
    abel
  let e : ↥states ≃ ↥S × ↥W :=
    { toFun := fun q ↦
        (⟨label q.1, by
          have hret : MME.dwzAsymmetricAffineRetains
              levelSum S I J K q.1 := by
            have hq := (Finset.mem_filter.mp q.2).1
            simpa only [MME.dwzAsymmetricAffineStatesRetaining,
              Finset.mem_filter, Finset.mem_univ, true_and] using hq
          exact (mme_dwz_asymmetric_affine_retains_iff_weight_label
            hpodd levelSum S I J K hsupport q.1).mp hret |>.1⟩,
         ⟨toWeight q.1, (Finset.mem_filter.mp q.2).2⟩)
      invFun := fun sw ↦
        ⟨mkState sw.1 sw.2, by
          apply Finset.mem_filter.mpr
          refine ⟨?_, ?_⟩
          · simp only [MME.dwzAsymmetricAffineStatesRetaining,
              Finset.mem_filter, Finset.mem_univ, true_and]
            apply (mme_dwz_asymmetric_affine_retains_iff_weight_label
              hpodd levelSum S I J K hsupport (mkState sw.1 sw.2)).mpr
            refine ⟨?_, ?_⟩
            · change label (mkState sw.1 sw.2) ∈ S
              rw [hmkLabel]
              exact sw.1.2
            · simp only [mkState, Fin.lastCases_castSucc]
          · change toWeight (mkState sw.1 sw.2) ∈ W
            rw [hmkWeight]
            exact sw.2.2⟩
      left_inv := fun q ↦ by
        apply Subtype.ext
        apply Prod.ext
        · funext i
          refine Fin.lastCases ?_ (fun t ↦ ?_) i
          · have hnormal :=
            (mme_dwz_asymmetric_affine_retains_iff_weight_label
                hpodd levelSum S I J K hsupport q.1).mp
                (by
                  have hq := (Finset.mem_filter.mp q.2).1
                  simpa only [MME.dwzAsymmetricAffineStatesRetaining,
                    Finset.mem_filter, Finset.mem_univ, true_and] using hq)
            simp only [mkState, label, toWeight, Fin.lastCases_last]
            abel
          · simp only [mkState, toWeight, Fin.lastCases_castSucc]
        · have hnormal :=
            (mme_dwz_asymmetric_affine_retains_iff_weight_label
              hpodd levelSum S I J K hsupport q.1).mp
              (by
                have hq := (Finset.mem_filter.mp q.2).1
                simpa only [MME.dwzAsymmetricAffineStatesRetaining,
                  Finset.mem_filter, Finset.mem_univ, true_and] using hq)
          simpa only [mkState, toWeight] using hnormal.2.symm
      right_inv := fun sw ↦ by
        apply Prod.ext
        · apply Subtype.ext
          exact hmkLabel sw.1 sw.2
        · apply Subtype.ext
          exact hmkWeight sw.1 sw.2 }
  have hcard := Fintype.card_congr e
  simpa only [states, Fintype.card_coe, Fintype.card_prod] using hcard
