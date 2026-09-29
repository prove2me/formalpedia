-- Prove2me | solution 1 for mme_paired_matrix_cartesian_word_projection_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T03:56:38.0569+00:00
-- url     : https://prove2.me/submissions/7d9310c1-06a2-47c3-b3d3-f9b7dc7fb3d0

import Theorems.Thm_mme_paired_oriented_matrix_power_word_basis_maps
import Theorems.Thm_mme_MMObj_rectangle_mask_cardinality_restriction
import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.LinearAlgebra.StdBasis

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u v
set_option autoImplicit false

/-- Commuting coordinate maps transport a restriction after applying projections. -/
theorem mme_tensor_projection_restriction
    {K : Type u} [Field K] {d : ℕ} {T S : TensorObj K d}
    (f : ∀ i, T.V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f T.t = S.t)
    (P : ∀ i, T.V i →ₗ[K] T.V i)
    (Q : ∀ i, S.V i →ₗ[K] S.V i)
    (hcomm : ∀ i, (Q i).comp (f i) = (f i).comp (P i)) :
    TensorObj.Restrict { S with t := PiTensorProduct.map Q S.t }
      { T with t := PiTensorProduct.map P T.t } := by
  refine ⟨f, ?_⟩
  change PiTensorProduct.map f (PiTensorProduct.map P T.t) =
    PiTensorProduct.map Q S.t
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  simp_rw [← hcomm]
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hf]

/-- A map specified on bases commutes with retaining any set of target labels
and its preimage among source labels. Injectivity is not required. -/
theorem mme_basis_map_projection
    {K : Type u} [Field K] {V W : Type u}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {α β : Type u} (b : Basis α K V) (c : Basis β K W)
    (f : V →ₗ[K] W) (g : α → β) (hf : ∀ a, f (b a) = c (g a))
    (keep : β → Prop) [DecidablePred keep] :
    (c.constr K (fun a ↦ if keep a then c a else 0)).comp f =
      f.comp (b.constr K (fun a ↦ if keep (g a) then b a else 0)) := by
  apply b.ext
  intro a
  simp only [LinearMap.comp_apply, Basis.constr_basis, hf]
  split_ifs <;> simp [hf]

/-- Simultaneous basis projections preserve a restriction when each coordinate
map carries source basis vectors to the specified target basis vectors. -/
theorem mme_tensor_basis_projection_restriction
    {K : Type u} [Field K] {d : ℕ} {T S : TensorObj K d}
    {α β : Fin d → Type u}
    (b : ∀ i, Basis (α i) K (T.V i)) (c : ∀ i, Basis (β i) K (S.V i))
    (f : ∀ i, T.V i →ₗ[K] S.V i) (g : ∀ i, α i → β i)
    (hf : PiTensorProduct.map f T.t = S.t)
    (hb : ∀ i a, f i (b i a) = c i (g i a))
    (keep : ∀ i, β i → Prop) [∀ i, DecidablePred (keep i)] :
    TensorObj.Restrict
      { S with t := (PiTensorProduct.map
        (fun i ↦ (c i).constr K (fun a ↦ if keep i a then c i a else 0)) S.t) }
      { T with t := (PiTensorProduct.map
        (fun i ↦ (b i).constr K (fun a ↦ if keep i (g i a) then b i a else 0)) T.t) } := by
  apply mme_tensor_projection_restriction f hf
  intro i
  exact mme_basis_map_projection (b i) (c i) (f i) (g i) (hb i) (keep i)

/-- Projecting one coordinate commutes with a restriction when its basis labels
are transported by the coordinate map. The other coordinates are unrestricted. -/
theorem mme_tensor_single_basis_projection_restriction
    {K : Type u} [Field K] {d : ℕ} {T S : TensorObj K d}
    (j : Fin d) {α β : Type u}
    (b : Basis α K (T.V j)) (c : Basis β K (S.V j))
    (f : ∀ i, T.V i →ₗ[K] S.V i) (g : α → β)
    (hf : PiTensorProduct.map f T.t = S.t)
    (hb : ∀ a, f j (b a) = c (g a))
    (keep : β → Prop) [DecidablePred keep] :
    TensorObj.Restrict
      { S with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) j
            (c.constr K (fun a ↦ if keep a then c a else 0))) S.t) }
      { T with t := (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) j
            (b.constr K (fun a ↦ if keep (g a) then b a else 0))) T.t) } := by
  apply mme_tensor_projection_restriction f hf
  intro i
  by_cases h : i = j
  · subst i
    simp only [Function.update_self]
    exact mme_basis_map_projection b c (f j) g hb keep
  · simp [Function.update_of_ne h]

/-- Selecting vectors of the coordinate basis is the entrywise mask by the
same predicate, including when the basis index type is universe-lifted. -/
theorem mme_coordinate_basis_projection_eq_mask
    {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (keep : ι → Prop) [DecidablePred keep] :
    let b := (Pi.basisFun K ι).reindex Equiv.ulift.symm
    b.constr K (fun a : ULift.{u} ι ↦ if keep a.down then b a else 0) =
      LinearMap.pi (fun i ↦ if keep i then LinearMap.proj i else 0) := by
  intro b
  apply b.ext
  intro a
  rw [Basis.constr_basis]
  funext i
  change (if keep a.down then b a else 0) i =
    (if keep i then LinearMap.proj i else 0) (b a)
  have hb : b a = Pi.single a.down (1 : K) := by
    exact ((Pi.basisFun K ι).reindex_apply Equiv.ulift.symm a).trans
      (Pi.basisFun_apply K ι a.down)
  rw [hb]
  by_cases h : i = a.down
  · subst i
    split_ifs <;> simp
  · split_ifs <;> simp [h]

/-- A Cartesian selection of the two oriented matrix word bases retains
one matrix block with exactly the selected word cardinalities. -/
theorem solution
    {K : Type u} [Field K] (q N : ℕ)
    (keepX : PowIndex (ULift.{u} (Fin 1 × Fin q)) N → Prop)
    (keepY : PowIndex (ULift.{u} (Fin q × Fin 1)) N → Prop)
    [DecidablePred keepX] [DecidablePred keepY] :
    let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 q 1)
    let V := TensorObj.permObj cyclicPerm (MMObj K 1 q 1)
    let c := (Pi.basisFun K (Fin 1 × Fin q)).reindex Equiv.ulift.symm
    let e := (Pi.basisFun K (Fin q × Fin 1)).reindex Equiv.ulift.symm
    let B := (kronPowModeBasis U 2 c N).tensorProduct (kronPowModeBasis V 2 e N)
    let source := (U.kronPow N).kron (V.kronPow N)
    let P : ∀ i, source.V i →ₗ[K] source.V i :=
      Function.update (fun _ ↦ LinearMap.id) 2
        (B.constr K (fun w ↦ if keepX w.1 ∧ keepY w.2 then B w else 0))
    TensorObj.Restrict
      (MMObj K (Fintype.card {x // keepX x}) 1 (Fintype.card {y // keepY y}))
      { source with t := PiTensorProduct.map P source.t } := by
  intro U V c e B source P
  obtain ⟨F, rows, cols, hF, hb⟩ :=
    mme_paired_oriented_matrix_power_word_basis_maps (K := K) q N
  let D := (Pi.basisFun K (Fin (q^N) × Fin (q^N))).reindex Equiv.ulift.symm
  let g := fun w : PowIndex (ULift.{u} (Fin 1 × Fin q)) N ×
      PowIndex (ULift.{u} (Fin q × Fin 1)) N ↦
    (⟨(rows w.2, cols w.1)⟩ : ULift.{u} (Fin (q^N) × Fin (q^N)))
  let C := fun i ↦ keepX (cols.symm i)
  let R := fun k ↦ keepY (rows.symm k)
  let keep := fun a : ULift.{u} (Fin (q^N) × Fin (q^N)) ↦ R a.down.1 ∧ C a.down.2
  have hbase : ∀ w, F 2 (B w) = D (g w) := by
    rintro ⟨x,y⟩
    dsimp only [B]
    erw [Basis.tensorProduct_apply]
    rw [hb]
    exact (((Pi.basisFun K (Fin (q^N) × Fin (q^N))).reindex_apply
      Equiv.ulift.symm (g (x,y))).trans
        (Pi.basisFun_apply K (Fin (q^N) × Fin (q^N)) (rows y,cols x))).symm
  have hproject := mme_tensor_single_basis_projection_restriction
    (T := source) (S := MMObj K (q^N) 1 (q^N)) 2 B D F g hF hbase keep
  have hsource : B.constr K (fun a ↦ if keep (g a) then B a else 0) =
      B.constr K (fun a ↦ if keepX a.1 ∧ keepY a.2 then B a else 0) := by
    apply B.ext
    intro a
    simp only [Basis.constr_basis]
    have hk : keep (g a) ↔ keepX a.1 ∧ keepY a.2 := by
      change (keepY (rows.symm (rows a.2)) ∧ keepX (cols.symm (cols a.1))) ↔ _
      rw [rows.symm_apply_apply, cols.symm_apply_apply, and_comm]
    exact if_congr hk rfl rfl
  have hmask := mme_coordinate_basis_projection_eq_mask (K := K)
    (ι := Fin (q^N) × Fin (q^N)) (fun ki ↦ R ki.1 ∧ C ki.2)
  erw [hsource, hmask] at hproject
  have hrectangle := mme_MMObj_rectangle_mask_cardinality_restriction
    (K := K) (q^N) 1 (q^N) C R
  have hC : Fintype.card {i : Fin (q^N) // C i} = Fintype.card {x // keepX x} :=
    Fintype.card_congr (Equiv.subtypeEquivOfSubtype cols.symm)
  have hR : Fintype.card {k : Fin (q^N) // R k} = Fintype.card {y // keepY y} :=
    Fintype.card_congr (Equiv.subtypeEquivOfSubtype rows.symm)
  rw [hC, hR] at hrectangle
  exact hrectangle.trans hproject

#print axioms solution
