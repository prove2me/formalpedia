-- Prove2me | solution 1 for mme_basis_all_allowed_subtensor_mono
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:04:05.600508+00:00
-- url     : https://prove2.me/submissions/f747ecb1-e678-4d1a-88c5-e6f3e7a8bde2

import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes

open MME Module
universe u

/-- Enlarging every allowed set preserves the smaller projected tensor as an
actual restriction of the larger projected tensor. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (small large : (i : Fin 3) → ι i → Prop)
    (h : ∀ i j, small i j → large i j) :
    TensorObj.Restrict (T.basisAllAllowedSubtensor b small)
      (T.basisAllAllowedSubtensor b large) := by
  classical
  let G := T.basisAllAllowedGrading b small
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes T _ b large
    (fun i => G.blockProj i 0) rfl
  intro i j hj
  have hs : ¬ small i j := fun hs => hj (h i j hs)
  have hx : b i j ∈ G.classOf i 1 := by
    change b i j ∈ Submodule.span K
      (b i '' {a | (if small i a then (0 : Fin 2) else 1) = 1})
    exact Submodule.subset_span ⟨j, by simp only [Set.mem_setOf_eq, if_neg hs], rfl⟩
  apply Subtype.ext
  change (((G.modeLequiv i).symm (b i j)) 0 : T.V i) = 0
  exact congrArg Subtype.val ((G.is_internal i).ofBijective_coeLinearMap_of_mem_ne
    (show (1 : Fin 2) ≠ 0 by decide) hx)


#print axioms solution
