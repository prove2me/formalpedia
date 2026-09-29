-- Prove2me | solution 1 for mme_complete_split_restrictedPower_basis_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:14:13.473229+00:00
-- url     : https://prove2.me/submissions/9f570d00-5214-4f0a-b250-94752354942f

import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_kronPowModeMap_recursive_basis
import Theorems.Thm_mme_kronPow_modewise_maps_preserve_tensor

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction Module
open scoped Classical NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem disallowed_projection_zero
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop) (i : Fin 3) (j : ι i)
    (hj : ¬ allowed i j) :
    (T.basisAllAllowedGrading b allowed).blockProj i 0 (b i j) = 0 := by
  classical
  let G := T.basisAllAllowedGrading b allowed
  have hx : b i j ∈ G.classOf i 1 := by
    change b i j ∈ cwBasisGrade (b i)
      (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 1
    exact Submodule.subset_span
      ⟨j, by simp only [Set.mem_setOf_eq, if_neg hj], rfl⟩
  exact (G.is_internal i).ofBijective_coeLinearMap_of_mem_ne
    (show (1 : Fin 2) ≠ 0 by decide) hx

/-- A literal basis-labelled tensor router preserves the simultaneous
complete-profile restriction at every finite power and tolerance. -/
theorem solution
    {K : Type u} [Field K] (T S : TensorObj K 3)
    {I J : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (I i) K (T.V i))
    (c : (i : Fin 3) → Basis (J i) K (S.V i))
    (f : (i : Fin 3) → T.V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f T.t = S.t)
    (idx : (i : Fin 3) → I i → J i)
    (hbasis : ∀ i a, f i (b i a) = c i (idx i a))
    {ell : ℕ}
    (labelT : (i : Fin 3) → I i → CompleteWord ell)
    (labelS : (i : Fin 3) → J i → CompleteWord ell)
    (hlabel : ∀ i a, labelS i (idx i a) = labelT i a)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Restrict (restrictedPower S c labelS beta epsilon N)
      (restrictedPower T b labelT beta epsilon N) := by
  classical
  let G := (S.kronPow N).basisAllAllowedGrading
    (fun i ↦ kronPowModeBasis S i (c i) N)
    (fun i ↦ ApproxConsistent (labelS i) (beta i) epsilon)
  let powerMap := fun i ↦ kronPowModeMap i (f i) N
  let maps := fun i ↦ (G.blockProj i 0).comp (powerMap i)
  have hmap : PiTensorProduct.map maps (T.kronPow N).t =
      (restrictedPower S c labelS beta epsilon N).t := by
    change PiTensorProduct.map
        (fun i ↦ (G.blockProj i 0).comp (powerMap i)) (T.kronPow N).t = _
    rw [PiTensorProduct.map_comp]
    change PiTensorProduct.map (fun i ↦ G.blockProj i 0)
      (PiTensorProduct.map powerMap (T.kronPow N).t) = _
    rw [mme_kronPow_modewise_maps_preserve_tensor f hf N]
    rfl
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes
    (T.kronPow N) (restrictedPower S c labelS beta epsilon N)
    (fun i ↦ kronPowModeBasis T i (b i) N)
    (fun i ↦ ApproxConsistent (labelT i) (beta i) epsilon) maps hmap
  intro i w hw
  change G.blockProj i 0
    (kronPowModeMap i (f i) N (kronPowModeBasis T i (b i) N w)) = 0
  rw [mme_kronPowModeMap_recursive_basis i (b i) (c i) (f i) (idx i) (hbasis i)]
  apply disallowed_projection_zero
  simpa only [ApproxConsistent, wordCount, PowIndex.get_ofFun, hlabel] using hw
