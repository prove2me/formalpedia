-- Prove2me | Theorems.Thm_mme_primary_hash_family_outerExtractionMap_word_eq_zero_of_mismatch
-- name    : mme_primary_hash_family_outerExtractionMap_word_eq_zero_of_mismatch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:15:54.420531+00:00
-- url     : https://prove2.me/theorems/1a538b18-d271-49f3-8491-aa37164a0712
-- title:
--   All-mode address-mismatch vanishing for the actual shared-Z family extraction maps
-- statement:
--   Let a three-graded tensor have a chosen basis in any one mode, with each basis vector killed by every block projector of a different grade. For any induced primary hash family, suppose a basis word in that mode disagrees at some position with every retained address $(a,h)$. Then the actual outer extraction map sends that word to zero. This applies to all three modes: the first two maps sum over $(a,h)$, whereas the third sums over $a$ and uses the family's distinguished representative of the shared third-mode address. The conclusion concerns the existing directional shared-Z family, not a scalar tensor or an independently extracted matrix-multiplication family. No support or nonzero-size assumption on the tensor is required for this map-vanishing statement.
-- source:
--   Finite projector bookkeeping for the enhanced 112 shared-Z construction in Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3, https://arxiv.org/abs/2210.10173. This is a formal all-mode adapter, not a separately numbered assertion in the paper. It uses exactly the existing public outerExtractionMap definition and generalizes the proved third-mode-only theorem mme_primary_hash_family_outerExtractionMap_Z_word_eq_zero_of_mismatch; the per-address tensor-product projector lemma is mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch.

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Definitions.Def_mme_kron_pow_mode_word_basis

open MME MME.DWZComponentRestriction PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false

theorem mme_primary_hash_family_outerExtractionMap_word_eq_zero_of_mismatch
    {K : Type u} [Field K]
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (i : Fin 3) {ι : Type u}
    (b : Basis ι K (T.V i)) (grade : ι → Fin 3)
    (hzero : ∀ (a : Fin 3) (j : ι), grade j ≠ a →
      grading.blockProj i a (b j) = 0)
    (w : PowIndex ι (2 * N))
    (hmismatch : ∀ (a : Fin A) (h : Fin H), ∃ r : Fin (2 * N),
      grade (PowIndex.get (2 * N) w r) ≠
        componentAddress family a h i r) :
    outerExtractionMap grading family i
        (kronPowModeBasis T i b (2 * N) w) = 0 := by sorry
