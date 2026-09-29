-- Prove2me | solution 1 for mme_kron_power_prefix_suffix_filter_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:23:07.982038+00:00
-- url     : https://prove2.me/submissions/674aefff-e1d3-4741-80ed-d6e38539def2

import Theorems.Thm_mme_kron_power_concatenation_basis_transport
import Definitions.Def_mme_tensor_rank

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

/-- Filters on the first factor's X words and the second factor's Y words
become prefix and suffix filters on a single tensor power. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) (n m : ℕ)
    {α β : Type u} (bX : Basis α K (T.V 0)) (bY : Basis β K (T.V 1))
    (P : (Fin m → α) → Prop) (Q : (Fin n → β) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    let X := T.kronPow m
    let Y := T.kronPow n
    let Z := T.kronPow (n + m)
    let bx := kronPowModeBasis T 0 bX m
    let basisY := kronPowModeBasis T 1 bY n
    let bzX := kronPowModeBasis T 0 bX (n + m)
    let bzY := kronPowModeBasis T 1 bY (n + m)
    let f : ∀ i, X.V i →ₗ[K] X.V i := Function.update (fun _ => LinearMap.id) 0
      (bx.constr K (fun w => if P (PowIndex.get m w) then bx w else 0))
    let g : ∀ i, Y.V i →ₗ[K] Y.V i := Function.update (fun _ => LinearMap.id) 1
      (basisY.constr K (fun w => if Q (PowIndex.get n w) then basisY w else 0))
    let h : ∀ i, Z.V i →ₗ[K] Z.V i := Function.update
      (Function.update (fun _ => LinearMap.id) 0
        (bzX.constr K (fun w =>
          if P (fun r => PowIndex.get (n + m) w ⟨r.val, by omega⟩) then bzX w else 0))) 1
      (bzY.constr K (fun w =>
        if Q (fun r => PowIndex.get (n + m) w ⟨m + r.val, by omega⟩) then bzY w else 0))
    TensorObj.Restrict { Z with t := PiTensorProduct.map h Z.t }
      (TensorObj.kron { X with t := PiTensorProduct.map f X.t }
        { Y with t := PiTensorProduct.map g Y.t }) := by
  intro X Y Z bx basisY bzX bzY f g h
  obtain ⟨F, hF, hb⟩ := mme_kron_power_concatenation_basis_transport T n m
  obtain ⟨joinX, hbX, hleft, _⟩ := hb 0 α bX
  obtain ⟨joinY, hbY, _, hright⟩ := hb 1 β bY
  have hcomp : (fun i => (F i).toLinearMap.comp (TensorProduct.map (f i) (g i))) =
      fun i => (h i).comp (F i).toLinearMap := by
    funext i
    fin_cases i
    · apply (bx.tensorProduct (kronPowModeBasis T 0 bX n)).ext
      rintro ⟨w, v⟩
      change F 0 (TensorProduct.map
        (bx.constr K (fun w => if P (PowIndex.get m w) then bx w else 0)) LinearMap.id
        ((bx.tensorProduct (kronPowModeBasis T 0 bX n)) (w, v))) =
        (bzX.constr K (fun z =>
          if P (fun r => PowIndex.get (n + m) z ⟨r.val, by omega⟩) then bzX z else 0))
          (F 0 ((bx.tensorProduct (kronPowModeBasis T 0 bX n)) (w, v)))
      rw [Basis.tensorProduct_apply, TensorProduct.map_tmul, Basis.constr_basis,
        LinearMap.id_apply, hbX, Basis.constr_basis]
      have hp : (fun r : Fin m => PowIndex.get (n + m) (joinX (w, v))
          ⟨r.val, by omega⟩) = PowIndex.get m w := funext (hleft w v)
      rw [hp]
      split_ifs with hpw
      · exact hbX w v
      · rw [TensorProduct.zero_tmul]
        exact (F 0).map_zero
    · apply ((kronPowModeBasis T 1 bY m).tensorProduct basisY).ext
      rintro ⟨w, v⟩
      change F 1 (TensorProduct.map LinearMap.id
        (basisY.constr K (fun v => if Q (PowIndex.get n v) then basisY v else 0))
        (((kronPowModeBasis T 1 bY m).tensorProduct basisY) (w, v))) =
        (bzY.constr K (fun z =>
          if Q (fun r => PowIndex.get (n + m) z ⟨m + r.val, by omega⟩) then bzY z else 0))
          (F 1 (((kronPowModeBasis T 1 bY m).tensorProduct basisY) (w, v)))
      rw [Basis.tensorProduct_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        Basis.constr_basis, hbY, Basis.constr_basis]
      have hq : (fun r : Fin n => PowIndex.get (n + m) (joinY (w, v))
          ⟨m + r.val, by omega⟩) = PowIndex.get n v := funext (hright w v)
      rw [hq]
      split_ifs with hqv
      · exact hbY w v
      · rw [TensorProduct.tmul_zero]
        exact (F 1).map_zero
    · change (F 2).toLinearMap.comp (TensorProduct.map LinearMap.id LinearMap.id) =
        LinearMap.id.comp (F 2).toLinearMap
      have hid : TensorProduct.map (LinearMap.id : X.V 2 →ₗ[K] X.V 2)
          (LinearMap.id : Y.V 2 →ₗ[K] Y.V 2) = LinearMap.id := by ext; rfl
      rw [hid]
      rfl
  refine ⟨fun i => (F i).toLinearMap, ?_⟩
  change PiTensorProduct.map (fun i => (F i).toLinearMap)
    (interchange (PiTensorProduct.map f X.t) (PiTensorProduct.map g Y.t)) =
      PiTensorProduct.map h Z.t
  rw [← TensorObj.TypeGrading.kronMap_interchange]
  change (PiTensorProduct.map (fun i => (F i).toLinearMap) ∘ₗ
    PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i)))
      (interchange X.t Y.t) = _
  rw [← PiTensorProduct.map_comp, hcomp, PiTensorProduct.map_comp,
    LinearMap.comp_apply, hF]

#print axioms solution
