-- Prove2me | solution 1 for mme_restrict_basisAllAllowedSubtensor_of_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T21:42:17.563061+00:00
-- url     : https://prove2.me/submissions/427ff98a-a98e-4aaf-898a-178b04a80c1a

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_tensor_rank

open MME Module PiTensorProduct
open scoped Classical

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem projection_on_basis
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop) (i : Fin 3) (j : ι i) :
    let G := T.basisAllAllowedGrading b allowed
    (G.classOf i 0).subtype (G.blockProj i 0 (b i j)) =
      if allowed i j then b i j else 0 := by
  classical
  dsimp only
  let G := T.basisAllAllowedGrading b allowed
  by_cases hj : allowed i j
  · rw [if_pos hj]
    have hx : b i j ∈ G.classOf i 0 := by
      change b i j ∈ cwBasisGrade (b i)
        (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 0
      exact Submodule.subset_span
        ⟨j, by simp only [Set.mem_setOf_eq, if_pos hj], rfl⟩
    change (((G.modeLequiv i).symm (b i j)) 0 : T.V i) = b i j
    exact congrArg Subtype.val
      ((G.is_internal i).ofBijective_coeLinearMap_of_mem hx)
  · rw [if_neg hj]
    have hx : b i j ∈ G.classOf i 1 := by
      change b i j ∈ cwBasisGrade (b i)
        (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 1
      exact Submodule.subset_span
        ⟨j, by simp only [Set.mem_setOf_eq, if_neg hj], rfl⟩
    change (((G.modeLequiv i).symm (b i j)) 0 : T.V i) = 0
    exact congrArg Subtype.val
      ((G.is_internal i).ofBijective_coeLinearMap_of_mem_ne
        (show (1 : Fin 2) ≠ 0 by decide) hx)

/-- An actual extraction descends through the simultaneous all-mode
projection if each mode map kills every disallowed basis vector. -/
theorem solution
    {K : Type u} [Field K] (T A : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop)
    (f : (i : Fin 3) → T.V i →ₗ[K] A.V i)
    (hmap : PiTensorProduct.map f T.t = A.t)
    (hvanish : ∀ i j, ¬ allowed i j → f i (b i j) = 0) :
    TensorObj.Restrict A (T.basisAllAllowedSubtensor b allowed) := by
  classical
  let G := T.basisAllAllowedGrading b allowed
  have hcomp : ∀ i,
      ((f i).comp (G.classOf i 0).subtype).comp (G.blockProj i 0) = f i := by
    intro i
    apply (b i).ext
    intro j
    change f i ((G.classOf i 0).subtype (G.blockProj i 0 (b i j))) = f i (b i j)
    rw [projection_on_basis]
    by_cases hj : allowed i j
    · rw [if_pos hj]
    · rw [if_neg hj, map_zero, hvanish i j hj]
  refine ⟨fun i ↦ (f i).comp (G.classOf i 0).subtype, ?_⟩
  change PiTensorProduct.map
      (fun i ↦ (f i).comp (G.classOf i 0).subtype)
      (PiTensorProduct.map (fun i ↦ G.blockProj i 0) T.t) = A.t
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  simpa only [hcomp] using hmap
