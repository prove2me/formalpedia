-- Prove2me | Theorems.Thm_mme_complete_split_power_projection_certificate
-- name    : mme_complete_split_power_projection_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T17:17:08.673988+00:00
-- url     : https://prove2.me/theorems/eee3ef34-4366-4edb-8d49-a8b11b74a029
-- title:
--   Complete-split powers are literal all-mode projections
-- statement:
--   The complete-split restricted Nth power is a restriction of the ordinary Nth tensor power. In every one of its three modes, the retained subspace is exactly the span of the canonical power-basis vectors satisfying the specified full-word count test. The theorem proves a finite zero-out operation only; supplied labels are not automatically identified with canonical CW words.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v3, printed pp.14-15, Definitions3.4-3.6. This is the finite all-mode projection layer; canonical CW labeling and the asymptotic degeneration/limit theorems remain separate.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_tensor_rank

set_option autoImplicit false

universe u

open MME MME.CompleteSplit MME.DWZComponentRestriction Module
open scoped NNReal

theorem mme_complete_split_power_projection_certificate
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Restrict (restrictedPower T b label beta epsilon N) (T.kronPow N) ∧
      ∀ i, ((T.kronPow N).basisAllAllowedGrading
        (fun j ↦ kronPowModeBasis T j (b j) N)
        (fun j ↦ ApproxConsistent (label j) (beta j) epsilon)).classOf i 0 =
          Submodule.span K ((kronPowModeBasis T i (b i) N) ''
            {w | ApproxConsistent (label i) (beta i) epsilon w}) := by sorry
