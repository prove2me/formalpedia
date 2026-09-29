-- Prove2me | solution 1 for mme_uniform_direct_sum_grading_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:22:00.154007+00:00
-- url     : https://prove2.me/submissions/608e4449-179c-43e3-8331-76d2c6a9f32e

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_diagObj_kron_isomorphic_bigAdd_const
import Theorems.Thm_mme_diagObj_kron_canonical_grading_certificate

open MME
universe u
set_option autoImplicit false

/-- A uniform direct-sum restriction admits a grading with exactly one supported
address per summand, disjoint in every mode. -/
theorem solution
    {K : Type u} [Field K] (S T : TensorObj K 3) (n : ℕ)
    (h : TensorObj.Restrict (TensorObj.bigAdd (fun _ : Fin n ↦ S)) T) :
    ∃ (P : TensorObj K 3) (t : ℕ) (grading : P.TypeGrading t)
        (C : Finset (Fin 3 → Fin t))
        (σs : Fin C.card → (Fin 3 → Fin t)),
      TensorObj.Restrict P T ∧
      (∀ j, σs j ∈ C) ∧
      Function.Injective σs ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
        ∀ i : Fin 3, σ i ≠ σ' i) ∧
      (∀ σ : Fin 3 → Fin t, σ ∉ C → grading.blockTensor σ = 0) ∧
      (∀ j, TensorObj.Restrict S (grading.blockSubtensor (σs j))) ∧
      C.card = n := by
  obtain ⟨t, grading, C, σs, hmem, hinj, hdisj, hsupp, hblocks, hcard⟩ :=
    mme_diagObj_kron_canonical_grading_certificate S n
  exact ⟨TensorObj.kron (TensorObj.diagObj K 3 n) S, t, grading, C, σs,
    (mme_diagObj_kron_isomorphic_bigAdd_const S n).1.trans h,
    hmem, hinj, hdisj, hsupp, hblocks, hcard⟩

#print axioms solution
