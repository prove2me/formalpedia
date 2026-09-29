-- Prove2me | solution 1 for mme_basisZAllowed_map_eq_zero_of_selected_singletons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T18:50:41.087465+00:00
-- url     : https://prove2.me/submissions/ef4380f2-c4b4-46ca-aacd-25da2d474d77

import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

private theorem piTensorProduct_map_update_zero
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin d) :
    PiTensorProduct.map (Function.update f i 0) = 0 := by
  have hzero := PiTensorProduct.map_update_smul
    f i (0 : K) (0 : V i →ₗ[K] W i)
  simpa only [zero_smul] using hzero

private theorem piTensorProduct_map_update_finset_sum
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {J : Type u} [DecidableEq J]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin d)
    (p : J → V i →ₗ[K] W i) (s : Finset J) (x : PiTensorProduct K V) :
    PiTensorProduct.map (Function.update f i (∑ j ∈ s, p j)) x =
      ∑ j ∈ s,
        PiTensorProduct.map (Function.update f i (p j)) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact LinearMap.congr_fun (piTensorProduct_map_update_zero f i) x
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        PiTensorProduct.map_update_add, LinearMap.add_apply, ih]

/-- A basis-backed Z mask kills a tensor if every selected singleton basis
slice kills it.  The maps before the mask are arbitrary; this is the exact
linear-algebra reduction needed for mixed-owner source tensors. -/
theorem solution
    {K : Type u} [Field K]
    {S T : TensorObj K 3} {I : Type u}
    [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (allowed : I → Prop)
    [DecidablePred allowed]
    (pre : ∀ i : Fin 3, S.V i →ₗ[K] T.V i)
    (hzero : ∀ j : I, allowed j →
      let G := T.basisZAllowedGrading bZ allowed
      let base : ∀ i : Fin 3, S.V i →ₗ[K] G.classOf i 0 :=
        fun i ↦ (G.blockProj i 0).comp (pre i)
      let singleton : T.V 2 →ₗ[K] T.V 2 :=
        MME.DWZComponentRestriction.basisLabelProjection bZ id {j}
      PiTensorProduct.map
        (Function.update base 2
          ((G.blockProj 2 0).comp singleton |>.comp (pre 2))) S.t = 0) :
    let G := T.basisZAllowedGrading bZ allowed
    PiTensorProduct.map
      (fun i ↦ (G.blockProj i 0).comp (pre i)) S.t = 0 := by
  classical
  dsimp only at hzero ⊢
  let G := T.basisZAllowedGrading bZ allowed
  let selected : Finset I := Finset.univ.filter allowed
  let base : ∀ i : Fin 3, S.V i →ₗ[K] G.classOf i 0 :=
    fun i ↦ (G.blockProj i 0).comp (pre i)
  let singleton : I → T.V 2 →ₗ[K] T.V 2 := fun j ↦
    MME.DWZComponentRestriction.basisLabelProjection bZ id {j}
  let piece : I → S.V 2 →ₗ[K] G.classOf 2 0 := fun j ↦
    ((G.blockProj 2 0).comp (singleton j)).comp (pre 2)
  have hproj : G.blockProj 2 0 =
      ∑ j ∈ selected, (G.blockProj 2 0).comp (singleton j) := by
    apply bZ.ext
    intro x
    change G.blockProj 2 0 (bZ x) =
      (∑ j ∈ selected,
        (G.blockProj 2 0).comp (singleton j)) (bZ x)
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    by_cases hx : allowed x
    · have hxsel : x ∈ selected := by simp only [selected, Finset.mem_filter,
          Finset.mem_univ, true_and]; exact hx
      rw [Finset.sum_eq_single x]
      · simp only [singleton,
          MME.DWZComponentRestriction.basisLabelProjection,
          Module.Basis.constr_basis, id_eq, Finset.mem_singleton, if_true]
      · intro y hy hne
        simp only [singleton,
          MME.DWZComponentRestriction.basisLabelProjection,
          Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
          if_neg (Ne.symm hne), map_zero]
      · exact fun hnot ↦ (hnot hxsel).elim
    · have hleft : G.blockProj 2 0 (bZ x) = 0 := by
        apply TensorObj.TypeGrading.blockProj_apply_mem_ne
          G 2 0 1 (by decide) (bZ x)
        change bZ x ∈ cwBasisGrade bZ
          (fun j ↦ if allowed j then 0 else 1) 1
        exact Submodule.subset_span
          ⟨x, by simp only [Set.mem_setOf_eq, if_neg hx], rfl⟩
      rw [hleft]
      symm
      apply Finset.sum_eq_zero
      intro y hy
      have hxy : x ≠ y := by
        intro hxy
        subst y
        exact hx (by
          simpa only [selected, Finset.mem_filter, Finset.mem_univ,
            true_and] using hy)
      simp only [singleton,
        MME.DWZComponentRestriction.basisLabelProjection,
        Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
        if_neg hxy, map_zero]
  have hmodeTwo : base 2 = ∑ j ∈ selected, piece j := by
    change (G.blockProj 2 0).comp (pre 2) = _
    rw [hproj]
    apply LinearMap.ext
    intro z
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, piece]
  have hbase : base = Function.update base 2 (∑ j ∈ selected, piece j) := by
    funext i
    by_cases hi : i = 2
    · subst i
      rw [Function.update_self]
      exact hmodeTwo
    · rw [Function.update_of_ne hi]
  change PiTensorProduct.map base S.t = 0
  rw [hbase, piTensorProduct_map_update_finset_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hjAllowed : allowed j := by
    simpa only [selected, Finset.mem_filter, Finset.mem_univ,
      true_and] using hj
  simpa only [base, piece, singleton, G] using hzero j hjAllowed
