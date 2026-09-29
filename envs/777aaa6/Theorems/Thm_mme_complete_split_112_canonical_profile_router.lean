-- Prove2me | Theorems.Thm_mme_complete_split_112_canonical_profile_router
-- name    : mme_complete_split_112_canonical_profile_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:24:42.291471+00:00
-- url     : https://prove2.me/theorems/b4340c3f-ef01-48d7-a6ae-f4cab5516061
-- title:
--   The canonical CW square112 router preserves all three complete profiles
-- statement:
--   Let $K$ be any field and $q$ any nonnegative integer. Let $T_{112}$ be the actual canonical $(1,1,2)$ block of $\mathrm{CW}_q^{\otimes2}$, and $C_q$ its explicit coupled-coordinate representation. For every triple $\beta$ of level-two complete profiles, nonnegative tolerance $\varepsilon$, and power $N$,
--
--   $$C_q^{\otimes N}[\beta_X,\beta_Y,\beta_Z,\varepsilon]\;\leq_{\rm restr}\;T_{112}^{\otimes N}[\beta_X,\beta_Y,\beta_Z,\varepsilon].$$
--
--   The canonical source uses both literal fine grades of every canonical basis pair; the coupled target uses the concrete internal grade's full two-letter word. No identification between an arbitrary grading and these labels is assumed. All three modes and every canonical coarse-block basis vector are covered. This is a finite profile-preserving restriction, not a tensor-value or asymptotic extraction assumption.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 (printed pp14–15). Finite specialization using the actual Coppersmith–Winograd square112 maps: accepted general-q full-basis router, concrete fine-word certificate, and simultaneous restricted-power functoriality. Exhaustive coarse-class basis coverage supplies the decoder, so the statement is not limited to a hand-selected list of vectors.

import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_CW_square_canonical_112_full_basis_router
import Theorems.Thm_mme_complete_split_restrictedPower_basis_router
import Theorems.Thm_mme_complete_split_112_coupled_basis_label_certificate

open MME MME.CompleteSplit112 MME.CompleteSplit MME.DWZComponentRestriction Module
open scoped Classical NNReal

universe u v

set_option autoImplicit false

theorem mme_complete_split_112_canonical_profile_router
    (K : Type u) [Field K] (q : ℕ)
    (beta : Fin 3 → Profile 2) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Restrict
      (restrictedPower (coupledObj K q) (liftedCoordBasis K q)
        (fun s ↦ fineWord s ∘ liftedCoordGrade q s) beta epsilon N)
      (restrictedCanonicalPower K q beta epsilon N) := by sorry
