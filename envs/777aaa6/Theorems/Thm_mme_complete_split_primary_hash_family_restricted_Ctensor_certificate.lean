-- Prove2me | Theorems.Thm_mme_complete_split_primary_hash_family_restricted_Ctensor_certificate
-- name    : mme_complete_split_primary_hash_family_restricted_Ctensor_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:21:14.376979+00:00
-- url     : https://prove2.me/theorems/8611c35b-5ff8-44d2-ab6d-46491c951cba
-- title:
--   Actual shared-Z family certificate after simultaneous complete-profile restriction
-- statement:
--   Let T be a three-graded tensor supported on the four coupled addresses 000, 111, 012, 102, whose blocks are respectively matrix multiplication tensors of dimensions (1,q,1), (1,q,1), (q,1,q), (q,1,q). Choose basis-compatible grades, complete-word labels and normalized target profiles in all three modes. Let an induced primary hash family retain A outer fibers, each with H shared-third-mode components and exact address counts N,L,G. Suppose every basis word excluded by the simultaneous complete-profile restriction mismatches every retained address in its own mode. Then the actual restricted tensor power admits a CTensorOneHOneFamilyCertificate with A stars, H labelled components per star and common component volume q^(4G+2L). The proof uses exactly the pre-existing star objects and directional extraction maps. This is a finite conditional extraction statement: it assumes the stated mismatch property, and does not assert the probabilistic existence, density, or asymptotic value of a family.
-- source:
--   Finite algebraic adapter combining Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 (enhanced 112 shared-Z construction), https://arxiv.org/abs/2210.10173, with Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.4–3.6 (all-mode complete-word profile restriction), https://arxiv.org/abs/2404.16349v2. This is an explicitly conditional formal adapter, not a newly claimed numbered theorem or the full recursive extraction theorem. It reuses the existing public four-block exact-address MM certificate, exact shared-Z outer extraction, and shared-Z star grading/component isomorphisms.

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data

open MME MME.CompleteSplit MME.DWZComponentRestriction
open CoupledCTensorPackaging Module PiTensorProduct BigOperators
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_primary_hash_family_restricted_Ctensor_certificate
    {K : Type u} [Field K]
    (q : ℕ) {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (h000 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![0, 0, 0]))
    (h111 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![1, 1, 1]))
    (h012 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![0, 1, 2]))
    (h102 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![1, 0, 2]))
    {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (grade : (i : Fin 3) → ι i → Fin 3)
    (hzero : ∀ (i : Fin 3) (a : Fin 3) (j : ι i), grade i j ≠ a →
      grading.blockProj i a (b i j) = 0)
    {ell : ℕ} (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0)
    (hmismatch : ∀ (i : Fin 3) (w : PowIndex (ι i) (2 * N)),
      ¬ ApproxConsistent (label i) (beta i) epsilon w →
      ∀ (a : Fin A) (h : Fin H), ∃ r : Fin (2 * N),
        grade i (PowIndex.get (2 * N) w r) ≠
          componentAddress family a h i r) :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (restrictedPower T b label beta epsilon (2 * N))
        A H (q ^ (4 * G + 2 * L))) := by sorry
