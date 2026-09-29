-- Prove2me | Theorems.Thm_mme_modern_CW_power_nonzero_coefficient_fine_support
-- name    : mme_modern_CW_power_nonzero_coefficient_fine_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T05:17:31.530324+00:00
-- url     : https://prove2.me/theorems/dca14bbd-93ac-4de3-8cbf-c6a87931d0df
-- title:
--   A nonzero literal CW power coefficient supplies full-word fine support
-- statement:
--   Let $B=2^{\max(\ell-1,0)}$, and consider the actual tensor $CW_q^{\otimes NB}$ over any field, expressed in the tensor product of its canonical ordered coordinate-word bases. Group the fine positions into $N$ consecutive chunks of length $B$. If the joint basis coefficient at three coordinate words $w_X,w_Y,w_Z$ is nonzero, then every chunk $t$ and every fine letter $r$ give a nonzero canonical one-copy CW block:
--
--   $$
--
--   [CW_q^{\otimes NB}]_{w_X,w_Y,w_Z}\ne0
--   \quad\Longrightarrow\quad
--   (CW_q)_{g(w_X(t,r)),\,g(w_Y(t,r)),\,g(w_Z(t,r))}\ne0.
--
--   $$
--
--   Here $g$ is the actual canonical coordinate grade and the flattening is the fixed ordered Fin-product equivalence. The conclusion concerns all letters of each full word, not only its grade sum. The harmless ULift changes only the index universe. All $q,N$ are allowed, including zero. No support or compatibility predicate is assumed.
-- source:
--   Derived from the literal Coppersmith–Winograd tensor, its canonical coordinate grading, and the exact tensor-power coefficient product identity. Source application: Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.4–3.6 (printed pp. 14–15), Remark 5.2 and Claims 5.7/5.10 (pp. 19–24), https://arxiv.org/abs/2404.16349v2. Reuses the complete coefficient-product proof from research/root_dwz_step2_hole/publish_kronpow_position_theorem/Solution.lean without its old heartbeat override. This is the actual coefficient-to-pointwise-support input to mme_modern_CW_full_word_boundary_histograms and hence to the boundary portion of grouped Y/Z compatibility; it is not the whole global extraction.

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Algebra.BigOperators.Fin

open MME MME.TensorObj MME.DWZStep1Support MME.CompleteSplit
open PiTensorProduct TensorProduct BigOperators Module

universe u

set_option autoImplicit false

theorem mme_modern_CW_power_nonzero_coefficient_fine_support
    {K : Type u} [Field K] (q ell N : ℕ)
    (w : Fin 3 → Fin (N * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2)))
    (hcoeff :
      (Basis.piTensorProduct (fun i ↦
        kronPowModeWordBasis (CWObj K q) i
          ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm)
          (N * 2 ^ (ell - 1)))).repr
        ((CWObj K q).kronPow (N * 2 ^ (ell - 1))).t w ≠ 0) :
    ∀ t : Fin N, ∀ r : Fin (2 ^ (ell - 1)),
      (cwThreeCanonicalGrading K q).blockTensor
        (fun i ↦ cwSquareCoordGrade q
          (w i (finProdFinEquiv (t, r))).down) ≠ 0 := by sorry
