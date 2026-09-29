-- Prove2me | solution 1 for mme_dwz_q6_121_common_halving_ambient_component_source_maps
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:20:35.261979+00:00
-- url     : https://prove2.me/submissions/814291f2-4d00-4bb8-9d83-3685815b4adb

import Theorems.Thm_mme_dwz_q6_canonical_121_swap_power_to_211_basis_transport
import Theorems.Thm_mme_dwz_q6_common_halving_paired_component_source_maps
import Definitions.Def_mme_dwz_component_pair_projection_data

open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction
open Module TensorProduct
universe u
set_option autoImplicit false

/-- The literal unprojected 121 pair routes to the paired oriented powers,
with every excluded Z-word pair killed by each retained component projection. -/
theorem solution
    {K : Type u} [Field K] (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component 13 * m) L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let N := DWZTable2Counts.component 13 * m
    let target := TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)
    ∃ maps : ∀ i, (componentPairAmbient K 13 m).V i →ₗ[K] target.V i,
      PiTensorProduct.map maps (componentPairAmbient K 13 m).t = target.t ∧
      ∀ w₁ w₂,
        (¬ componentWordAllowed 13 m w₁ ∨ ¬ componentWordAllowed 13 m w₂) →
        ∀ p : Fin A × Fin H,
          ((componentProj (K := K) family halving p 2).comp (maps 2))
            (componentPowerZBasis K 13 m w₁ ⊗ₜ[K]
              componentPowerZBasis K 13 m w₂) = 0 := by
  let N := DWZTable2Counts.component 13 * m
  obtain ⟨swap, hswap, hbasis⟩ :=
    mme_dwz_q6_canonical_121_swap_power_to_211_basis_transport K N
  obtain ⟨router, hrouter, hzero⟩ :=
    mme_dwz_q6_common_halving_paired_component_source_maps
      (K := K) 13 (Or.inl rfl) m rfl family halving
  let pair : ∀ i, (componentPairAmbient K 13 m).V i →ₗ[K]
      (TensorObj.kron ((canonicalComponentBlock K 13).kronPow N)
        ((canonicalComponentBlock K 14).kronPow N)).V i :=
    fun i ↦ TensorProduct.map LinearMap.id (swap i)
  refine ⟨fun i ↦ (router i).comp (pair i), ?_, ?_⟩
  · rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    have hp : PiTensorProduct.map pair (componentPairAmbient K 13 m).t =
        (TensorObj.kron ((canonicalComponentBlock K 13).kronPow N)
          ((canonicalComponentBlock K 14).kronPow N)).t := by
      change PiTensorProduct.map (fun i ↦ TensorProduct.map LinearMap.id (swap i))
        (interchange ((canonicalComponentBlock K 13).kronPow N).t
          (TensorObj.permObj swapFirstTwoPerm
            ((canonicalComponentBlock K 13).kronPow N)).t) = _
      rw [TensorObj.TypeGrading.kronMap_interchange, hswap, PiTensorProduct.map_id]
      rfl
    rw [hp]
    exact hrouter
  · intro w₁ w₂ hbad p
    change componentProj (K := K) family halving p 2
      (router 2 (pair 2 (_ ⊗ₜ[K] _))) = 0
    change componentProj (K := K) family halving p 2
      (router 2 (TensorProduct.map LinearMap.id (swap 2)
        (componentPowerZBasis K 13 m w₁ ⊗ₜ[K]
          componentPowerZBasis K 13 m w₂))) = 0
    erw [TensorProduct.map_tmul]
    change componentProj (K := K) family halving p 2
      (router 2 (componentPowerZBasis K 13 m w₁ ⊗ₜ[K]
        swap 2 (componentPowerZBasis K 13 m w₂))) = 0
    rw [show swap 2 (componentPowerZBasis K 13 m w₂) =
      kronPowModeBasis (canonicalComponentBlock K 14) 2
        (canonicalComponentZBasis K 14) N w₂ from hbasis w₂]
    exact hzero w₁ w₂ hbad p
