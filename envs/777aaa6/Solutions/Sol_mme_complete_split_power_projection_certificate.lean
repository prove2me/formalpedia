-- Prove2me | solution 1 for mme_complete_split_power_projection_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T17:17:20.244741+00:00
-- url     : https://prove2.me/submissions/86cfcca6-73c3-4a45-965a-f3a10478949c

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_tensor_rank

set_option autoImplicit false
set_option warningAsError true

universe u

open MME MME.CompleteSplit MME.DWZComponentRestriction Module
open scoped NNReal

private theorem basisAllAllowed_projection
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop) :
    TensorObj.Restrict (T.basisAllAllowedSubtensor b allowed) T ∧
      ∀ i, (T.basisAllAllowedGrading b allowed).classOf i 0 =
        Submodule.span K ((b i) '' {j | allowed i j}) := by
  classical
  constructor
  · exact ⟨fun i ↦ (T.basisAllAllowedGrading b allowed).blockProj i 0, rfl⟩
  · intro i
    change cwBasisGrade (b i)
      (fun j ↦ if allowed i j then (0 : Fin 2) else 1) 0 = _
    simp only [cwBasisGrade]
    congr 2
    ext j
    simp


theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Restrict (restrictedPower T b label beta epsilon N) (T.kronPow N) ∧
      ∀ i, ((T.kronPow N).basisAllAllowedGrading
        (fun j ↦ kronPowModeBasis T j (b j) N)
        (fun j ↦ ApproxConsistent (label j) (beta j) epsilon)).classOf i 0 =
          Submodule.span K ((kronPowModeBasis T i (b i) N) ''
            {w | ApproxConsistent (label i) (beta i) epsilon w}) := by
  exact (basisAllAllowed_projection (T.kronPow N)
    (fun i ↦ kronPowModeBasis T i (b i) N)
    (fun i ↦ ApproxConsistent (label i) (beta i) epsilon))
