-- Prove2me | solution 1 for mme_dwz_q6_211_common_halving_ambient_component_source_maps
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:31:47.691204+00:00
-- url     : https://prove2.me/submissions/f911ef4f-f362-443c-a953-87a85746471c

import Theorems.Thm_mme_dwz_q6_canonical_211_swap_power_to_121_basis_transport
import Theorems.Thm_mme_dwz_q6_common_halving_paired_component_source_maps
import Definitions.Def_mme_dwz_component_pair_projection_data

open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction
open Module TensorProduct
universe u
set_option autoImplicit false

namespace MME.Canonical211AmbientSourceMaps

private theorem interchange_tprod {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (PiTensorProduct.tprod K v) (PiTensorProduct.tprod K w) =
      PiTensorProduct.tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- `interchange` is commutative up to `TensorProduct.comm`. -/
private theorem interchange_comm {K : Type u} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W) :
    PiTensorProduct.map (fun i => (TensorProduct.comm K (W i) (V i)).toLinearMap)
      (interchange b a) = interchange a b := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod c' w =>
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      rw [interchange_tprod, PiTensorProduct.map_tprod, interchange_tprod, mul_comm c c']
      congr 2
    | add x y ih1 ih2 => simp only [map_add, LinearMap.add_apply, ih1, ih2]
  | add x y ih1 ih2 => simp only [LinearMap.add_apply, map_add, ih1, ih2]

private theorem comm_map_tmul {K : Type u} [Field K]
    {V W U : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (f : W →ₗ[K] U) (v : V) (w : W) :
    (TensorProduct.comm K V U) (TensorProduct.map LinearMap.id f (v ⊗ₜ[K] w)) =
      f w ⊗ₜ[K] v := by
  rw [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.comm_tmul]

end MME.Canonical211AmbientSourceMaps

/-- The literal unprojected 211 pair routes to the paired oriented powers,
with every excluded Z-word pair killed by each retained component projection. -/
theorem solution
    {K : Type u} [Field K] (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component 14 * m) L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let N := DWZTable2Counts.component 14 * m
    let target := TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)
    ∃ maps : ∀ i, (componentPairAmbient K 14 m).V i →ₗ[K] target.V i,
      PiTensorProduct.map maps (componentPairAmbient K 14 m).t = target.t ∧
      ∀ w₁ w₂,
        (¬ componentWordAllowed 14 m w₁ ∨ ¬ componentWordAllowed 14 m w₂) →
        ∀ p : Fin A × Fin H,
          ((componentProj (K := K) family halving p 2).comp (maps 2))
            (componentPowerZBasis K 14 m w₁ ⊗ₜ[K]
              componentPowerZBasis K 14 m w₂) = 0 := by
  let N := DWZTable2Counts.component 14 * m
  obtain ⟨swap, hswap, hbasis⟩ :=
    mme_dwz_q6_canonical_211_swap_power_to_121_basis_transport K N
  obtain ⟨router, hrouter, hzero⟩ :=
    mme_dwz_q6_common_halving_paired_component_source_maps
      (K := K) 14 (Or.inr rfl) m rfl family halving
  let pair : ∀ i, (componentPairAmbient K 14 m).V i →ₗ[K]
      (TensorObj.kron ((canonicalComponentBlock K 13).kronPow N)
        ((canonicalComponentBlock K 14).kronPow N)).V i :=
    fun i ↦ (TensorProduct.comm K _ _).toLinearMap.comp
      (TensorProduct.map LinearMap.id (swap i))
  refine ⟨fun i ↦ (router i).comp (pair i), ?_, ?_⟩
  · rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    have hp : PiTensorProduct.map pair (componentPairAmbient K 14 m).t =
        (TensorObj.kron ((canonicalComponentBlock K 13).kronPow N)
          ((canonicalComponentBlock K 14).kronPow N)).t := by
      change PiTensorProduct.map (fun i ↦
        (TensorProduct.comm K _ _).toLinearMap.comp
          (TensorProduct.map LinearMap.id (swap i)))
        (interchange ((canonicalComponentBlock K 14).kronPow N).t
          (TensorObj.permObj swapFirstTwoPerm
            ((canonicalComponentBlock K 14).kronPow N)).t) = _
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply,
        TensorObj.TypeGrading.kronMap_interchange, hswap, PiTensorProduct.map_id]
      exact MME.Canonical211AmbientSourceMaps.interchange_comm _ _
    rw [hp]
    exact hrouter
  · intro w₁ w₂ hbad p
    have hpair : pair 2 (componentPowerZBasis K 14 m w₁ ⊗ₜ[K]
        componentPowerZBasis K 14 m w₂) =
        kronPowModeBasis (canonicalComponentBlock K 13) 2
          (canonicalComponentZBasis K 13) N w₂ ⊗ₜ[K]
        componentPowerZBasis K 14 m w₁ := by
      change (TensorProduct.comm K _ _)
        (TensorProduct.map LinearMap.id (swap 2)
          (componentPowerZBasis K 14 m w₁ ⊗ₜ[K]
            componentPowerZBasis K 14 m w₂)) = _
      rw [MME.Canonical211AmbientSourceMaps.comm_map_tmul]
      exact congrArg (fun z ↦ z ⊗ₜ[K] componentPowerZBasis K 14 m w₁) (hbasis w₂)
    change componentProj (K := K) family halving p 2
      (router 2 (pair 2 (_ ⊗ₜ[K] _))) = 0
    rw [hpair]
    exact hzero w₂ w₁ hbad.symm p
