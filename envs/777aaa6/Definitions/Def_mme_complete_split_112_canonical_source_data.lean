-- Prove2me | Definitions.Def_mme_complete_split_112_canonical_source_data
-- name    : mme_complete_split_112_canonical_source_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-06T22:14:11.902261+00:00
-- url     : https://prove2.me/theorems/c222f976-9a98-4caf-af16-5f99d2c0f967
-- title:
--   Literal canonical 112 bases and all-three-mode complete profiles
-- statement:
--   For any field and any nonnegative q, take the actual canonical (1,1,2) constituent of the CW square. Its three mode bases are the inherited canonical coarse-class subset bases. Label every basis vector with both literal level-one CW grades in tensor-factor order. Apply the existing simultaneous complete-profile restriction at arbitrary power and nonnegative tolerance. These definitions introduce no extraction maps, profile-preservation assertions, or tensor-value hypotheses.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 (printed pp14–15). Specialization to the canonical square112 constituent; reuses the existing coarseClassBasis and LiftedCoarsePair definitions from the prior DWZ mission without restricting to q6 or to modeZ.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_complete_split_profile_projection

set_option autoImplicit false
set_option warningAsError true

open Module
open scoped NNReal

universe u

namespace MME.CompleteSplit112

/-- The actual canonical 112 constituent of the CW square, at arbitrary q. -/
noncomputable def canonicalObj (K : Type u) [Field K] (q : ℕ) : TensorObj K 3 :=
  (cwSquareCanonicalGrading K q).blockSubtensor (cwSquareBlockType 1 1 2)

/-- Universe-lifted canonical pairs in each of the three coarse classes. -/
abbrev CanonicalCoord (q : ℕ) (s : Fin 3) : Type u :=
  DWZComponentRestriction.LiftedCoarsePair.{u} q (cwSquareBlockType 1 1 2 s)

/-- The subset basis inherited from the actual CW square coordinate basis. -/
noncomputable def canonicalBasis (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (CanonicalCoord.{u} q s) K ((canonicalObj K q).V s) :=
  (DWZComponentRestriction.coarseClassBasis (K := K) q s
    (cwSquareBlockType 1 1 2 s)).reindex Equiv.ulift.symm

/-- Both literal fine grades, in the original CW tensor-factor order. -/
def canonicalLabel (q : ℕ) (s : Fin 3) (p : CanonicalCoord.{u} q s) :
    CompleteSplit.CompleteWord 2 :=
  ![cwSquareCoordGrade q p.down.1.1, cwSquareCoordGrade q p.down.1.2]

/-- Definition 3.6 applied to the actual canonical 112 source, with all modes
filtered. No coupled-tensor replacement or value assertion is built in. -/
noncomputable def restrictedCanonicalPower (K : Type u) [Field K] (q : ℕ)
    (beta : Fin 3 → CompleteSplit.Profile 2) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj K 3 :=
  CompleteSplit.restrictedPower (canonicalObj K q) (canonicalBasis K q)
    (canonicalLabel q) beta epsilon N

end MME.CompleteSplit112


