-- Prove2me | solution 1 for mme_MMObj_rectangle_mask_cardinality_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T03:40:41.623971+00:00
-- url     : https://prove2.me/submissions/07d2826e-9cb9-45d6-9caf-8e2eb9a1e644

import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_permutation
import Mathlib.Tactic.FinCases

open MME PiTensorProduct Module BigOperators
universe u
set_option autoImplicit false

private noncomputable def matrixSubspaceMap
    {K : Type u} [Field K] {n m p a c : ℕ}
    (cols : Fin a → Fin n) (rows : Fin c → Fin p) :
    ∀ i, (MMObj K n m p).V i →ₗ[K] (MMObj K a m c).V i
  | ⟨0, _⟩ => LinearMap.pi (fun ij ↦ LinearMap.proj (cols ij.1, ij.2))
  | ⟨1, _⟩ => LinearMap.pi (fun jk ↦ LinearMap.proj (jk.1, rows jk.2))
  | ⟨2, _⟩ => LinearMap.pi (fun ki ↦ LinearMap.proj (rows ki.1, cols ki.2))

private noncomputable def matrixPure (K : Type u) [Field K] (n m p : ℕ)
    (i : Fin n) (j : Fin m) (k : Fin p) : PiTensorProduct K (MMSpace K n m p) :=
  tprod K (fun s ↦ match s with
    | ⟨0, _⟩ => Pi.single (i,j) 1
    | ⟨1, _⟩ => Pi.single (j,k) 1
    | ⟨2, _⟩ => Pi.single (k,i) 1)

private theorem subspace_map_pure
    {K : Type u} [Field K] {n m p a c : ℕ}
    (cols : Fin a → Fin n) (rows : Fin c → Fin p)
    (hc : Function.Injective cols) (hr : Function.Injective rows)
    (i : Fin a) (j : Fin m) (k : Fin c) :
    PiTensorProduct.map (matrixSubspaceMap (K := K) (m := m) cols rows)
      (matrixPure K n m p (cols i) j (rows k)) = matrixPure K a m c i j k := by
  classical
  unfold matrixPure
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s
  · funext ⟨i', j'⟩
    change (Pi.single (cols i,j) 1 : Fin n × Fin m → K) (cols i',j') =
      (Pi.single (i,j) 1 : Fin a × Fin m → K) (i',j')
    simp only [Pi.single_apply, Prod.mk.injEq, hc.eq_iff]
  · funext ⟨j', k'⟩
    change (Pi.single (j,rows k) 1 : Fin m × Fin p → K) (j',rows k') =
      (Pi.single (j,k) 1 : Fin m × Fin c → K) (j',k')
    simp only [Pi.single_apply, Prod.mk.injEq, hr.eq_iff]
  · funext ⟨k', i'⟩
    change (Pi.single (rows k,cols i) 1 : Fin p × Fin n → K) (rows k',cols i') =
      (Pi.single (k,i) 1 : Fin c × Fin a → K) (k',i')
    simp only [Pi.single_apply, Prod.mk.injEq, hc.eq_iff, hr.eq_iff]

private theorem subspace_map_pure_zero_col
    {K : Type u} [Field K] {n m p a c : ℕ}
    (cols : Fin a → Fin n) (rows : Fin c → Fin p)
    (i : Fin n) (hi : i ∉ Set.range cols) (j : Fin m) (k : Fin p) :
    PiTensorProduct.map (matrixSubspaceMap (K := K) (m := m) cols rows)
      (matrixPure K n m p i j k) = 0 := by
  classical
  unfold matrixPure
  erw [PiTensorProduct.map_tprod]
  apply (PiTensorProduct.tprod K).map_coord_zero 0
  funext x
  change (Pi.single (i,j) 1 : Fin n × Fin m → K) (cols x.1,x.2) = (0 : K)
  have h : cols x.1 ≠ i := fun h ↦ hi ⟨x.1,h⟩
  simp [h]

private theorem subspace_map_pure_zero_row
    {K : Type u} [Field K] {n m p a c : ℕ}
    (cols : Fin a → Fin n) (rows : Fin c → Fin p)
    (i : Fin n) (j : Fin m) (k : Fin p) (hk : k ∉ Set.range rows) :
    PiTensorProduct.map (matrixSubspaceMap (K := K) (m := m) cols rows)
      (matrixPure K n m p i j k) = 0 := by
  classical
  unfold matrixPure
  erw [PiTensorProduct.map_tprod]
  apply (PiTensorProduct.tprod K).map_coord_zero 1
  funext x
  change (Pi.single (j,k) 1 : Fin m × Fin p → K) (x.1,rows x.2) = (0 : K)
  have h : rows x.2 ≠ k := fun h ↦ hk ⟨x.2,h⟩
  simp [h]

/-- Restricting matrix coordinates along injective row and column selections
preserves the corresponding smaller matrix multiplication tensor. -/
theorem mme_MMObj_submatrix_basis_maps
    {K : Type u} [Field K] {n m p a c : ℕ}
    (cols : Fin a → Fin n) (rows : Fin c → Fin p)
    (hc : Function.Injective cols) (hr : Function.Injective rows) :
    ∃ f : ∀ i, (MMObj K n m p).V i →ₗ[K] (MMObj K a m c).V i,
      PiTensorProduct.map f (MMObj K n m p).t = (MMObj K a m c).t ∧
      ∀ v : Fin p × Fin n → K, ∀ k i, f 2 v (k,i) = v (rows k,cols i) := by
  classical
  let f := matrixSubspaceMap (K := K) (m := m) cols rows
  refine ⟨f, ?_, fun _ _ _ ↦ rfl⟩
  change PiTensorProduct.map f (∑ i, ∑ j, ∑ k, matrixPure K n m p i j k) =
    ∑ i, ∑ j, ∑ k, matrixPure K a m c i j k
  simp only [map_sum]
  have hcols := Fintype.sum_of_injective cols hc
    (fun i ↦ ∑ j, ∑ k, PiTensorProduct.map f (matrixPure K n m p (cols i) j k))
    (fun i ↦ ∑ j, ∑ k, PiTensorProduct.map f (matrixPure K n m p i j k))
    (fun i hi ↦ by simp [f, subspace_map_pure_zero_col cols rows i hi])
    (fun _ ↦ rfl)
  rw [← hcols]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (Fintype.sum_of_injective rows hr
    (fun k ↦ matrixPure K a m c i j k)
    (fun k ↦ PiTensorProduct.map f (matrixPure K n m p (cols i) j k))
    (fun k hk ↦ subspace_map_pure_zero_row cols rows (cols i) j k hk)
    (fun k ↦ (subspace_map_pure cols rows hc hr i j k).symm)).symm

/-- Any selected rectangle whose rows and columns survive the shared-coordinate
mask restricts to the matrix multiplication tensor on that rectangle. -/
theorem mme_MMObj_rectangle_mask_restriction
    {K : Type u} [Field K] {n m p a c : ℕ}
    (cols : Fin a → Fin n) (rows : Fin c → Fin p)
    (hc : Function.Injective cols) (hr : Function.Injective rows)
    (C : Fin n → Prop) (R : Fin p → Prop) [DecidablePred C] [DecidablePred R]
    (hC : ∀ i, C (cols i)) (hR : ∀ k, R (rows k)) :
    let P : ∀ i, (MMObj K n m p).V i →ₗ[K] (MMObj K n m p).V i :=
      Function.update (fun _ ↦ LinearMap.id) 2
        (LinearMap.pi (fun ki : Fin p × Fin n ↦
          if R ki.1 ∧ C ki.2 then LinearMap.proj ki else 0))
    TensorObj.Restrict (MMObj K a m c)
      { MMObj K n m p with t := PiTensorProduct.map P (MMObj K n m p).t } := by
  intro P
  obtain ⟨f, hf, hthird⟩ := mme_MMObj_submatrix_basis_maps (K := K) (m := m)
    cols rows hc hr
  have hcomp : (fun i ↦ (f i).comp (P i)) = f := by
    funext i
    by_cases hi : i = 2
    · subst i
      apply LinearMap.ext
      intro v
      funext x
      rcases x with ⟨k,i⟩
      change f 2 (P 2 v) (k,i) = f 2 v (k,i)
      rw [hthird, hthird]
      change (if R (rows k) ∧ C (cols i) then
        LinearMap.proj (rows k,cols i) else 0) v = v (rows k,cols i)
      simp [hR, hC]
    · simp [P, Function.update_of_ne hi]
  refine ⟨f, ?_⟩
  change PiTensorProduct.map f (PiTensorProduct.map P (MMObj K n m p).t) = _
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp, hcomp]
  exact hf

/-- A rectangular shared-coordinate mask retains a matrix tensor whose outer
dimensions are exactly the numbers of selected columns and rows. -/
theorem solution
    {K : Type u} [Field K] (n m p : ℕ)
    (C : Fin n → Prop) (R : Fin p → Prop) [DecidablePred C] [DecidablePred R] :
    let P : ∀ i, (MMObj K n m p).V i →ₗ[K] (MMObj K n m p).V i :=
      Function.update (fun _ ↦ LinearMap.id) 2
        (LinearMap.pi (fun ki : Fin p × Fin n ↦
          if R ki.1 ∧ C ki.2 then LinearMap.proj ki else 0))
    TensorObj.Restrict
      (MMObj K (Fintype.card {i : Fin n // C i}) m (Fintype.card {k : Fin p // R k}))
      { MMObj K n m p with t := PiTensorProduct.map P (MMObj K n m p).t } := by
  let cols := fun i : Fin (Fintype.card {i : Fin n // C i}) ↦
    ((Fintype.equivFin {i : Fin n // C i}).symm i).val
  let rows := fun k : Fin (Fintype.card {k : Fin p // R k}) ↦
    ((Fintype.equivFin {k : Fin p // R k}).symm k).val
  have hc : Function.Injective cols :=
    Subtype.val_injective.comp (Fintype.equivFin {i : Fin n // C i}).symm.injective
  have hr : Function.Injective rows :=
    Subtype.val_injective.comp (Fintype.equivFin {k : Fin p // R k}).symm.injective
  exact mme_MMObj_rectangle_mask_restriction cols rows hc hr C R
    (fun i ↦ ((Fintype.equivFin {i : Fin n // C i}).symm i).property)
    (fun k ↦ ((Fintype.equivFin {k : Fin p // R k}).symm k).property)

#print axioms solution
