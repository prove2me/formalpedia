-- Prove2me | solution 1 for mme_dwz_step1_filtered_mixed_raw_tensor_eq_singleton_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:30:14.201117+00:00
-- url     : https://prove2.me/submissions/5b30dcb6-9cd9-429b-a268-956876cebee0

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data

open MME PiTensorProduct

universe u uR uI uS uT

set_option autoImplicit false
set_option warningAsError true

open MME.DWZGlobalCorrelated

private theorem map_eq_of_pointwise
    {R : Type uR} [CommSemiring R]
    {ι : Type uI}
    {S : ι → Type uS} [∀ i, AddCommMonoid (S i)]
      [∀ i, Module R (S i)]
    {T : ι → Type uT} [∀ i, AddCommMonoid (T i)]
      [∀ i, Module R (T i)]
    (f g : ∀ i, S i →ₗ[R] T i)
    (h : ∀ i, f i = g i)
    (x : PiTensorProduct R S) :
    PiTensorProduct.map f x = PiTensorProduct.map g x := by
  have hfg : f = g := funext h
  rw [hfg]

private theorem post_comp_proj_eq_source_map
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : MME.DWZSourceAligned.AddressZWord
      (sourceWord reindex edge owner))
    (i : Fin 3) :
    (step1FilteredMixedSingletonPost K m reindex q edge
        competitor owner W i).comp
        (gradedAddressProj (cwSquareCanonicalGrading K 6) L
          (step1MixedAddress reindex edge competitor owner) i) =
      step1FilteredMixedSingletonMaps K m reindex q edge
        competitor owner W i := by
  unfold step1FilteredMixedSingletonPost
    step1FilteredMixedSingletonMaps
    step1MixedCoarseProj
  rw [LinearMap.comp_assoc]

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : MME.DWZSourceAligned.AddressZWord
      (sourceWord reindex edge owner)) :
    step1FilteredMixedRawTensor K m reindex q edge competitor owner W =
      PiTensorProduct.map
        (step1FilteredMixedSingletonMaps K m reindex q edge
          competitor owner W)
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t := by
  unfold step1FilteredMixedRawTensor
  apply map_eq_of_pointwise
  intro i
  unfold step1FilteredMixedRawMaps
  exact post_comp_proj_eq_source_map
    m reindex q edge competitor owner W i
