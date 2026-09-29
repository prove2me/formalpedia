-- Prove2me | solution 1 for mme_dwz_q6_common_halving_union_word_projection_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T02:50:17.557907+00:00
-- url     : https://prove2.me/submissions/3b26ad9d-9b8c-4c7c-8016-acead6794de1

import Theorems.Thm_mme_dwz_q6_canonical_121_211_paired_powered_basis_labelled_source_router
import Theorems.Thm_mme_dwz_q6_121_211_common_halving_disallowed_word_mismatches_halves
import Theorems.Thm_mme_dwz_q6_canonical_121_swap_power_to_211_basis_transport
import Theorems.Thm_mme_dwz_q6_canonical_211_swap_power_to_121_basis_transport
import Theorems.Thm_mme_dwz_component_pair_restriction_of_disallowed_word_vanishing
import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data

open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction
open Module TensorProduct
universe u
set_option autoImplicit false

namespace MME.PairedWordSourceDescent

private def WordVanishing {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    {U : Type u} [AddCommGroup U] [Module K U]
    (post : (TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).V 2 →ₗ[K] U) : Prop :=
  ∀ (wX wY : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N),
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) x.down
    ((¬ ∃ p : Fin A × Fin H, ∀ r,
      grade (PowIndex.get N wX r) =
        (family.entry p).val 0 (halving.position (Sum.inl r))) ∨
     (¬ ∃ p : Fin A × Fin H, ∀ r,
      grade (PowIndex.get N wY r) =
        (family.entry p).val 1 (halving.position (Sum.inr r)))) →
    post (kronPowModeBasis
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)) 2
        ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N wX ⊗ₜ[K]
      kronPowModeBasis (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
        ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N wY) = 0

/-- The canonical paired source maps carry excluded words to words absent
from every relevant family half-address. -/
private theorem paired_source_maps
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = MME.DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    {U : Type u} [AddCommGroup U] [Module K U]
    (post : (TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).V 2 →ₗ[K] U)
    (hpost : WordVanishing family halving post) :
    ∃ maps : ∀ i : Fin 3,
        (TensorObj.kron
          ((canonicalComponentBlock K (13 : Fin 15)).kronPow N)
          ((canonicalComponentBlock K (14 : Fin 15)).kronPow N)).V i →ₗ[K]
        (TensorObj.kron
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow N)
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).V i,
      PiTensorProduct.map maps
          (TensorObj.kron
            ((canonicalComponentBlock K (13 : Fin 15)).kronPow N)
            ((canonicalComponentBlock K (14 : Fin 15)).kronPow N)).t =
        (TensorObj.kron
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow N)
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t ∧
      ∀ (w13 w14 : PowIndex (LiftedCoarsePair.{u} 6 1) N),
        ((¬ ∀ a : Fin 3,
          Fintype.card {r : Fin N // (PowIndex.get N w13 r).leftGrade = a} =
            MME.DWZTable2Counts.split s a * m) ∨
         (¬ ∀ a : Fin 3,
          Fintype.card {r : Fin N // (PowIndex.get N w14 r).leftGrade = a} =
            MME.DWZTable2Counts.split s a * m)) →
        (post.comp (maps 2))
            (kronPowModeBasis (canonicalComponentBlock K (13 : Fin 15)) 2
                (canonicalComponentZBasis K (13 : Fin 15)) N w13 ⊗ₜ[K]
              kronPowModeBasis (canonicalComponentBlock K (14 : Fin 15)) 2
                (canonicalComponentZBasis K (14 : Fin 15)) N w14) = 0 := by
  obtain ⟨coord, hcoord, maps, htensor, hbasis⟩ :=
    mme_dwz_q6_canonical_121_211_paired_powered_basis_labelled_source_router K N
  refine ⟨maps, htensor, ?_⟩
  intro w13 w14 hbad
  rw [LinearMap.comp_apply, hbasis]
  apply hpost
  have hmismatch := mme_dwz_q6_121_211_common_halving_disallowed_word_mismatches_halves
    s hs m hN family halving coord hcoord
  rcases hbad with h13 | h14
  · left
    rintro ⟨p, hp⟩
    obtain ⟨r, hr⟩ := hmismatch.1 w13 h13 p
    exact hr (by simpa using hp r)
  · right
    rintro ⟨p, hp⟩
    obtain ⟨r, hr⟩ := hmismatch.2 w14 h14 p
    exact hr (by simpa using hp r)


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


/-- The literal unprojected 121 pair routes to the paired oriented powers,
with every excluded Z-word pair killed by the postcomposed map. -/
private theorem ambient_121_maps
    {K : Type u} [Field K] (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component 13 * m) L G A H)
    (halving : family.CommonBalancedXYHalving)
    {U : Type u} [AddCommGroup U] [Module K U]
    (post : (TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow
        (DWZTable2Counts.component 13 * m))
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow
        (DWZTable2Counts.component 13 * m))).V 2 →ₗ[K] U)
    (hpost : WordVanishing family halving post) :
    let N := DWZTable2Counts.component 13 * m
    let target := TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)
    ∃ maps : ∀ i, (componentPairAmbient K 13 m).V i →ₗ[K] target.V i,
      PiTensorProduct.map maps (componentPairAmbient K 13 m).t = target.t ∧
      ∀ w₁ w₂,
        (¬ componentWordAllowed 13 m w₁ ∨ ¬ componentWordAllowed 13 m w₂) →
        (post.comp (maps 2))
            (componentPowerZBasis K 13 m w₁ ⊗ₜ[K]
              componentPowerZBasis K 13 m w₂) = 0 := by
  let N := DWZTable2Counts.component 13 * m
  obtain ⟨swap, hswap, hbasis⟩ :=
    mme_dwz_q6_canonical_121_swap_power_to_211_basis_transport K N
  obtain ⟨router, hrouter, hzero⟩ :=
    paired_source_maps
      (K := K) 13 (Or.inl rfl) m rfl family halving post hpost
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
  · intro w₁ w₂ hbad
    change post
      (router 2 (pair 2 (_ ⊗ₜ[K] _))) = 0
    change post
      (router 2 (TensorProduct.map LinearMap.id (swap 2)
        (componentPowerZBasis K 13 m w₁ ⊗ₜ[K]
          componentPowerZBasis K 13 m w₂))) = 0
    erw [TensorProduct.map_tmul]
    change post
      (router 2 (componentPowerZBasis K 13 m w₁ ⊗ₜ[K]
        swap 2 (componentPowerZBasis K 13 m w₂))) = 0
    rw [show swap 2 (componentPowerZBasis K 13 m w₂) =
      kronPowModeBasis (canonicalComponentBlock K 14) 2
        (canonicalComponentZBasis K 14) N w₂ from hbasis w₂]
    exact hzero w₁ w₂ hbad

/-- The literal unprojected 211 pair routes to the paired oriented powers,
with every excluded Z-word pair killed by the postcomposed map. -/
private theorem ambient_211_maps
    {K : Type u} [Field K] (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component 14 * m) L G A H)
    (halving : family.CommonBalancedXYHalving)
    {U : Type u} [AddCommGroup U] [Module K U]
    (post : (TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow
        (DWZTable2Counts.component 14 * m))
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow
        (DWZTable2Counts.component 14 * m))).V 2 →ₗ[K] U)
    (hpost : WordVanishing family halving post) :
    let N := DWZTable2Counts.component 14 * m
    let target := TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)
    ∃ maps : ∀ i, (componentPairAmbient K 14 m).V i →ₗ[K] target.V i,
      PiTensorProduct.map maps (componentPairAmbient K 14 m).t = target.t ∧
      ∀ w₁ w₂,
        (¬ componentWordAllowed 14 m w₁ ∨ ¬ componentWordAllowed 14 m w₂) →
        (post.comp (maps 2))
            (componentPowerZBasis K 14 m w₁ ⊗ₜ[K]
              componentPowerZBasis K 14 m w₂) = 0 := by
  let N := DWZTable2Counts.component 14 * m
  obtain ⟨swap, hswap, hbasis⟩ :=
    mme_dwz_q6_canonical_211_swap_power_to_121_basis_transport K N
  obtain ⟨router, hrouter, hzero⟩ :=
    paired_source_maps
      (K := K) 14 (Or.inr rfl) m rfl family halving post hpost
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
      exact interchange_comm _ _
    rw [hp]
    exact hrouter
  · intro w₁ w₂ hbad
    have hpair : pair 2 (componentPowerZBasis K 14 m w₁ ⊗ₜ[K]
        componentPowerZBasis K 14 m w₂) =
        kronPowModeBasis (canonicalComponentBlock K 13) 2
          (canonicalComponentZBasis K 13) N w₂ ⊗ₜ[K]
        componentPowerZBasis K 14 m w₁ := by
      change (TensorProduct.comm K _ _)
        (TensorProduct.map LinearMap.id (swap 2)
          (componentPowerZBasis K 14 m w₁ ⊗ₜ[K]
            componentPowerZBasis K 14 m w₂)) = _
      rw [comm_map_tmul]
      exact congrArg (fun z ↦ z ⊗ₜ[K] componentPowerZBasis K 14 m w₁) (hbasis w₂)
    change post
      (router 2 (pair 2 (_ ⊗ₜ[K] _))) = 0
    rw [hpair]
    exact hzero w₂ w₁ hbad.symm

end MME.PairedWordSourceDescent

/-- A paired-power restriction whose third map kills words absent from the
family half-addresses descends to the literal allowed-word component pair. -/
theorem mme_dwz_q6_paired_word_vanishing_restricted_source_descent
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (T : TensorObj K 3)
    (maps : ∀ i, (TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).V i →ₗ[K] T.V i)
    (htensor : PiTensorProduct.map maps (TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t = T.t)
    (hzero : ∀ (wX wY : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N),
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) x.down
    ((¬ ∃ p : Fin A × Fin H, ∀ r,
      grade (PowIndex.get N wX r) =
        (family.entry p).val 0 (halving.position (Sum.inl r))) ∨
     (¬ ∃ p : Fin A × Fin H, ∀ r,
      grade (PowIndex.get N wY r) =
        (family.entry p).val 1 (halving.position (Sum.inr r)))) →
    maps 2 (kronPowModeBasis
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)) 2
        ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N wX ⊗ₜ[K]
      kronPowModeBasis (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
        ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N wY) = 0) :
    TensorObj.Restrict T (componentPairRestricted K s m) := by
  subst N
  have hsource : ∃ router : ∀ i, (componentPairAmbient K s m).V i →ₗ[K]
      (TensorObj.kron
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow
          (DWZTable2Counts.component s * m))
        ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow
          (DWZTable2Counts.component s * m))).V i,
      PiTensorProduct.map router (componentPairAmbient K s m).t =
        (TensorObj.kron
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow
            (DWZTable2Counts.component s * m))
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow
            (DWZTable2Counts.component s * m))).t ∧
      ∀ w₁ w₂,
        (¬ componentWordAllowed s m w₁ ∨ ¬ componentWordAllowed s m w₂) →
        ((maps 2).comp (router 2))
          (componentPowerZBasis K s m w₁ ⊗ₜ[K] componentPowerZBasis K s m w₂) = 0 := by
    rcases hs with rfl | rfl
    · exact MME.PairedWordSourceDescent.ambient_121_maps
        m L G A H family halving (maps 2) hzero
    · exact MME.PairedWordSourceDescent.ambient_211_maps
        m L G A H family halving (maps 2) hzero
  obtain ⟨router, hrouter, hsourcezero⟩ := hsource
  let composite := fun i ↦ (maps i).comp (router i)
  have hcomposite : PiTensorProduct.map composite (componentPairAmbient K s m).t = T.t := by
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hrouter, htensor]
  exact ⟨fun i ↦ (composite i).comp (componentPairInclusion K s m i),
    mme_dwz_component_pair_restriction_of_disallowed_word_vanishing
      s m T composite hcomposite hsourcezero⟩

/-- The union of the family's first-X and second-Y half words can be retained
as one aggregate Z projection of the literal restricted component pair. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let left := (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N
    let right := (TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N
    let paired := TensorObj.kron left right
    let bX := kronPowModeBasis
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)) 2
      ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N
    let bY := kronPowModeBasis (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
      ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N
    let basis := bX.tensorProduct bY
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) x.down
    let allowed := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N ×
        PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N ↦
      (∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N w.1 r) =
          (family.entry p).val 0 (halving.position (Sum.inl r))) ∧
      (∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N w.2 r) =
          (family.entry p).val 1 (halving.position (Sum.inr r)))
    letI : DecidablePred allowed := Classical.decPred _
    let projection : ∀ i, paired.V i →ₗ[K] paired.V i :=
      Function.update (fun _ ↦ LinearMap.id) 2
        (basis.constr K (fun w ↦ if allowed w then basis w else 0))
    TensorObj.Restrict { paired with t := PiTensorProduct.map projection paired.t }
      (componentPairRestricted K s m) := by
  dsimp only
  apply mme_dwz_q6_paired_word_vanishing_restricted_source_descent
    s hs m hN family halving _ _ rfl
  intro wX wY grade hbad
  simp only [Function.update_self]
  -- The projector and tensor basis inherit definitionally equal module instances.
  set_option backward.isDefEq.respectTransparency false in
    erw [← Basis.tensorProduct_apply, Basis.constr_basis]
  split_ifs with h
  · exact False.elim (hbad.elim (fun hx ↦ hx h.1) (fun hy ↦ hy h.2))
  · rfl
