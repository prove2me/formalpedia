-- Prove2me | Theorems.Thm_mme_CW_square_2376_profile_pruned_grading_of_orbit_certificate
-- name    : mme_CW_square_2376_profile_pruned_grading_of_orbit_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:59:04.784147+00:00
-- url     : https://prove2.me/theorems/b456f935-5926-424a-994b-5fa03d272d33
-- title:
--   Mode-disjoint exact-profile pruning for the CW 2.376 construction
-- statement:
--   Assume the concrete five-grade orbit certificate for the square of the Coppersmith--Winograd tensor at $q=6$. For every sufficiently large exact-profile scale $m$, the type-selection, Salem--Spencer hashing, and collision deletion steps produce a coordinate restriction $P_m$ of the source tensor
--
--   $$
--   T_6^{\otimes 6{,}000{,}000m}.
--   $$
--
--   The restricted tensor has a genuine mode grading and a retained address set $C_m$ with an injective enumeration. Distinct retained addresses differ in every mode, every block outside $C_m$ is zero, and every retained block restricts to the exact profile core
--
--   $$
--   \langle s_m,s_m,s_m\rangle\otimes\operatorname{cyc}(T_{112})^{\otimes616{,}627m},
--   \qquad s_m=12^{75{,}036m}38^{307{,}638m}.
--   $$
--
--   Moreover, with $H$ equal to the reciprocal marginal-entropy denominator from equation (13) and $r_m=(m+1)^{-1/4}$,
--
--   $$
--   \bigl(H e^{-r_m}\bigr)^{3{,}000{,}000m}\le |C_m|.
--   $$
--
--   This is the exact structural output of the finite pruning argument. In particular, it records tensor independence through mode-disjoint graded blocks rather than merely counting hash labels. Combined with the generic independent-block assembly theorem, it yields the direct sum of profile cores used in the $\omega<2.376$ proof.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equation (11), type counts (12)--(13), and Salem--Spencer hashing/collision pruning on journal pp. 265--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_CW_2376_profile_data
import Definitions.Def_mme_CW_square_five_grade_certificate
import Definitions.Def_mme_block_subtensor
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
open MME Filter
universe u

theorem mme_CW_square_2376_profile_pruned_grading_of_orbit_certificate
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6) :
    ∀ᶠ m : ℕ in atTop,
      ∃ (P : TensorObj K 3) (t : ℕ) (grading : P.TypeGrading t)
          (C : Finset (Fin 3 → Fin t))
          (σs : Fin C.card → (Fin 3 → Fin t)),
        TensorObj.Restrict P
            ((CWObj K 6).kronPow (6000000 * m)) ∧
        (∀ j, σs j ∈ C) ∧
        Function.Injective σs ∧
        (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
          ∀ i : Fin 3, σ i ≠ σ' i) ∧
        (∀ σ : Fin 3 → Fin t, σ ∉ C →
          grading.blockTensor σ = 0) ∧
        (∀ j, TensorObj.Restrict (cw2376ProfileCore K m)
          (grading.blockSubtensor (σs j))) ∧
        (cw2376ProfileCountBase *
            Real.exp (-(cw2376ProfileRate m))) ^
            (3000000 * m) ≤ (C.card : ℝ) := by
  sorry
