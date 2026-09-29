-- Prove2me | solution 1 for mme_dwz_q6_canonical_121_swap_power_to_211_basis_transport
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:20:34.816358+00:00
-- url     : https://prove2.me/submissions/420ac06c-a5df-45be-a533-4339176fa108

import Theorems.Thm_mme_dwz_q6_canonical_121_swap_to_211_basis_transport
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_TypeGrading_kron

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

namespace MME.CanonicalPairedPowerTransport

private noncomputable def powerMap
    {K : Type u} [Field K] {T S : TensorObj K 3}
    (f : ∀ i, (TensorObj.permObj swapFirstTwoPerm T).V i →ₗ[K] S.V i) :
    (n : ℕ) → ∀ i,
      (TensorObj.permObj swapFirstTwoPerm (T.kronPow n)).V i →ₗ[K]
        (S.kronPow n).V i
  | 0, _ => LinearMap.id
  | n + 1, i => TensorProduct.map (f i) (powerMap f n i)

private theorem powerMap_tensor
    {K : Type u} [Field K] {T S : TensorObj K 3}
    (f : ∀ i, (TensorObj.permObj swapFirstTwoPerm T).V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f (TensorObj.permObj swapFirstTwoPerm T).t = S.t) :
    ∀ n, PiTensorProduct.map (powerMap f n)
      (TensorObj.permObj swapFirstTwoPerm (T.kronPow n)).t = (S.kronPow n).t
  | 0 => by
      change PiTensorProduct.map (fun _ ↦ LinearMap.id)
        ((PiTensorProduct.reindex K (fun _ : Fin 3 ↦ K) swapFirstTwoPerm)
          (PiTensorProduct.tprod K (fun _ ↦ 1))) = _
      rw [PiTensorProduct.map_id, LinearMap.id_apply, PiTensorProduct.reindex_tprod]
      rfl
  | n + 1 => by
      change PiTensorProduct.map (fun i ↦ TensorProduct.map (f i) (powerMap f n i))
        ((PiTensorProduct.reindex K _ swapFirstTwoPerm)
          (interchange T.t (T.kronPow n).t)) = _
      rw [reindex_interchange, TensorObj.TypeGrading.kronMap_interchange]
      change interchange
        (PiTensorProduct.map f (TensorObj.permObj swapFirstTwoPerm T).t)
        (PiTensorProduct.map (powerMap f n)
          (TensorObj.permObj swapFirstTwoPerm (T.kronPow n)).t) = _
      rw [hf, powerMap_tensor f hf n]
      rfl

private theorem powerMap_basis
    {K : Type u} [Field K]
    (f : ∀ i, (TensorObj.permObj swapFirstTwoPerm
      (canonicalComponentBlock K (13 : Fin 15))).V i →ₗ[K]
      (canonicalComponentBlock K (14 : Fin 15)).V i)
    (hf : ∀ p : LiftedCoarsePair.{u} 6 1,
      f 2 (canonicalComponentZBasis K (13 : Fin 15) p) =
        canonicalComponentZBasis K (14 : Fin 15) p) :
    ∀ n (w : PowIndex (LiftedCoarsePair.{u} 6 1) n),
      powerMap f n 2
        (kronPowModeBasis (canonicalComponentBlock K (13 : Fin 15)) 2
          (canonicalComponentZBasis K (13 : Fin 15)) n w) =
      kronPowModeBasis (canonicalComponentBlock K (14 : Fin 15)) 2
        (canonicalComponentZBasis K (14 : Fin 15)) n w
  | 0, _ => rfl
  | n + 1, (p, w) => by
      change TensorProduct.map (f 2) (powerMap f n 2)
        ((Basis.tensorProduct (canonicalComponentZBasis K (13 : Fin 15))
          (kronPowModeBasis (canonicalComponentBlock K (13 : Fin 15)) 2
            (canonicalComponentZBasis K (13 : Fin 15)) n)) (p, w)) = _
      rw [Basis.tensorProduct_apply]
      erw [TensorProduct.map_tmul]
      rw [hf, powerMap_basis f hf n w]
      change _ = (Basis.tensorProduct (canonicalComponentZBasis K (14 : Fin 15))
        (kronPowModeBasis (canonicalComponentBlock K (14 : Fin 15)) 2
          (canonicalComponentZBasis K (14 : Fin 15)) n)) (p, w)
      rw [Basis.tensorProduct_apply]

end MME.CanonicalPairedPowerTransport

/-- The swapped canonical 121 power maps to the 211 power without changing
any third-mode word label. -/
theorem solution
    (K : Type u) [Field K] (n : ℕ) :
    ∃ maps : ∀ i,
      (TensorObj.permObj swapFirstTwoPerm
        ((canonicalComponentBlock K (13 : Fin 15)).kronPow n)).V i →ₗ[K]
      ((canonicalComponentBlock K (14 : Fin 15)).kronPow n).V i,
      PiTensorProduct.map maps
        (TensorObj.permObj swapFirstTwoPerm
          ((canonicalComponentBlock K (13 : Fin 15)).kronPow n)).t =
        ((canonicalComponentBlock K (14 : Fin 15)).kronPow n).t ∧
      ∀ w : PowIndex (LiftedCoarsePair.{u} 6 1) n,
        maps 2 (kronPowModeBasis (canonicalComponentBlock K (13 : Fin 15)) 2
          (canonicalComponentZBasis K (13 : Fin 15)) n w) =
        kronPowModeBasis (canonicalComponentBlock K (14 : Fin 15)) 2
          (canonicalComponentZBasis K (14 : Fin 15)) n w := by
  obtain ⟨f, hf, hb⟩ := mme_dwz_q6_canonical_121_swap_to_211_basis_transport K
  exact ⟨MME.CanonicalPairedPowerTransport.powerMap f n,
    MME.CanonicalPairedPowerTransport.powerMap_tensor f hf n,
    MME.CanonicalPairedPowerTransport.powerMap_basis f hb n⟩
