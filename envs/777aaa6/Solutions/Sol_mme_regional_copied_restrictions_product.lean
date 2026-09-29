-- Prove2me | solution 1 for mme_regional_copied_restrictions_product
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T15:13:25.232235+00:00
-- url     : https://prove2.me/submissions/b37763bf-74b3-4cc9-882b-b9ddd01a9de9

import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_bigAdd_mono_restrict

open BigOperators MME MME.TensorObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u

private theorem product_sums {K : Type u} [Field K] {k : ℕ}
    (S : Fin k → TensorObj K 3) (copies : Fin k → ℕ) :
    Isomorphic (kronFin k (fun j ↦ bigAdd (fun _ : Fin (copies j) ↦ S j)))
      (bigAdd (fun _ : Fin (∏ j, copies j) ↦ kronFin k S)) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [mme_toQ_kronFin, TensorQ.toQ_bigAdd]
  simp_rw [TensorQ.toQ_bigAdd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Nat.cast_prod, mme_toQ_kronFin]

theorem solution {K : Type u} [Field K] {k : ℕ}
    (source : TensorObj K 3) (S : Fin k → TensorObj K 3)
    (a b c inputs outputs : Fin k → ℕ)
    (hgroup : Restrict (kronFin k S) source)
    (h : ∀ j, Restrict (bigAdd (fun _ : Fin (outputs j) ↦ MMObj K (a j) (b j) (c j)))
      (bigAdd (fun _ : Fin (inputs j) ↦ S j))) :
    Restrict (bigAdd (fun _ : Fin (∏ j, outputs j) ↦ MMObj K (∏ j, a j) (∏ j, b j) (∏ j, c j)))
      (bigAdd (fun _ : Fin (∏ j, inputs j) ↦ source)) := by
  classical
  choose f hf using h
  have hk : Restrict
      (kronFin k (fun j ↦ bigAdd (fun _ : Fin (outputs j) ↦ MMObj K (a j) (b j) (c j))))
      (kronFin k (fun j ↦ bigAdd (fun _ : Fin (inputs j) ↦ S j))) :=
    ⟨kronFinFamilyModeMap k _ _ f, kronFinFamilyModeMap_preserves_tensor _ _ f hf⟩
  exact (mme_bigAdd_mono_restrict (fun _ : Fin (∏ j, outputs j) ↦
    (mme_kronFin_MMObj_iso k a b c).2)).trans
    ((product_sums (fun j ↦ MMObj K (a j) (b j) (c j)) outputs).2.trans
      (hk.trans ((product_sums S inputs).1.trans
        (mme_bigAdd_mono_restrict (fun _ : Fin (∏ j, inputs j) ↦ hgroup)))))
