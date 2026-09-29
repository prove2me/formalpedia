-- Prove2me | Definitions.Def_mme_complete_split_canonical_square_data
-- name    : mme_complete_split_canonical_square_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-07T01:19:01.067054+00:00
-- url     : https://prove2.me/theorems/8f60ad2f-c7c3-4e08-b004-6b8d168d501e
-- title:
--   Literal canonical CW-square blocks and all-mode complete profiles
-- statement:
--   For every field $K$, parameter $q$, and coarse square address $\rho$, define the actual canonical CW-square block, its inherited coarse-class subset bases, and the complete two-letter labels of those basis vectors in the original tensor-factor order. Apply simultaneous complete-profile restrictions in all three modes at any nonnegative tolerance and any power. These definitions specialize definitionally to the existing canonical $112$ data. They contain no source-isomorphism, basis-transport, profile-preservation, extraction, or tensor-value assumption.
-- source:
--   Canonical coarse-address generalization of existing Prove2Me mme_complete_split_112_canonical_source_data. More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions 3.4–3.6, pp. 14–15; implemented directly with the existing canonical CW-square grading, coarseClassBasis, LiftedCoarsePair, and all-mode CompleteSplit.restrictedPower.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_complete_split_profile_projection

open Module
open scoped NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.CompleteSplitCanonicalSquare

/-- The literal canonical CW-square block at an arbitrary coarse address. -/
noncomputable def obj (K : Type u) [Field K] (q : ℕ)
    (rho : Fin 3 → Fin 5) : TensorObj K 3 :=
  (cwSquareCanonicalGrading K q).blockSubtensor rho

/-- The actual coordinate pairs in each coarse class, lifted only in universe. -/
abbrev Coord (q : ℕ) (rho : Fin 3 → Fin 5) (i : Fin 3) : Type u :=
  DWZComponentRestriction.LiftedCoarsePair.{u} q (rho i)

/-- The canonical subset basis of the literal coarse block. -/
noncomputable def basis (K : Type u) [Field K] (q : ℕ)
    (rho : Fin 3 → Fin 5) (i : Fin 3) :
    Basis (Coord.{u} q rho i) K ((obj K q rho).V i) :=
  (DWZComponentRestriction.coarseClassBasis (K := K) q i (rho i)).reindex
    Equiv.ulift.symm

/-- Both fine grades in the original order of the two CW factors. -/
def label (q : ℕ) (rho : Fin 3 → Fin 5) (i : Fin 3)
    (p : Coord.{u} q rho i) : CompleteSplit.CompleteWord 2 :=
  ![cwSquareCoordGrade q p.down.1.1, cwSquareCoordGrade q p.down.1.2]

/-- Simultaneous complete-profile projection in all three modes. -/
noncomputable def restrictedPower (K : Type u) [Field K] (q : ℕ)
    (rho : Fin 3 → Fin 5) (beta : Fin 3 → CompleteSplit.Profile 2)
    (epsilon : ℝ≥0) (N : ℕ) : TensorObj K 3 :=
  CompleteSplit.restrictedPower (obj K q rho) (basis K q rho)
    (label q rho) beta epsilon N

end MME.CompleteSplitCanonicalSquare


