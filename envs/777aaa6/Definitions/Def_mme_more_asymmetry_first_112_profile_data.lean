-- Prove2me | Definitions.Def_mme_more_asymmetry_first_112_profile_data
-- name    : mme_more_asymmetry_first_112_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-06T21:27:29.545537+00:00
-- url     : https://prove2.me/theorems/1bf4020d-2621-4ba3-8c23-00b0c3a6b8b9
-- title:
--   More Asymmetry: exact first active 112 profile data
-- statement:
--   Fix the first positive fourth-power parent, shape $(1,1,6)$ in global region one, and its first square $(1,1,2)$ child in child region one from the released square-matrix witness. Let
--
--   $$p=\frac{8959763742786037}{2361183241434822606848}.$$
--
--   This is the exact rational representation of the stored IEEE double at parameter position 923. The unrotated $X,Y$ profiles assign mass $1/2$ to each of the words $01,10$; the $Z$ profile assigns $p,1-2p,p$ to $02,11,20$. Other words have mass zero. Cyclic left rotations permute the mode profiles. Also record the finite lexicographic shape construction, complementary-split child registration order, and four exact positive candidate weights identifying this active path.
--
--   These are raw rational data for a later certificate. No normalization, extraction, tensor value or full numerical feasibility is built into the definition.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu and Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.4–3.6 (printed pp.14–15) for complete split profiles. Exact released numerical specialization: OSF https://osf.io/mw5ak/, code_matrix_mult.zip v1 SHA256 a88d211df0a82f0bba0a77ccbad9103064ebef08eea95613e5926a4f666260d8, member data/W1.00_2.371339.mat SHA256 783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. The profile formulas are src/evaluation/TermInfoLv2.m lines134–146,180; scalar params(923), registered as square term2, parent11/region1, group181. Static incidence follows src/utils/PrepareShapes.m, PrepareSplits.m, src/evaluation/FindOrCreateTerm.m and TermInfo.Build. This is a finite source-data specialization, not the paper's extraction or numerical omega theorem.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_stothers_fourth_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096

open BigOperators

namespace MME.MoreAsymmetryFirstSlice

/-- Exact rational value of the IEEE double in released params(923), not a
rounded replacement. Its owner is square term 2, parent 11, child region 1. -/
def split0 : ℚ := 8959763742786037 / 2361183241434822606848

/-- Raw three-mode complete profiles of the selected 112 consumer. -/
def baseProbability (mode : Fin 3) (word : Fin 2 → Fin 3) : ℚ :=
  if mode.val = 2 then
    if ((word 0).val = 0 ∧ (word 1).val = 2) ∨ ((word 0).val = 2 ∧ (word 1).val = 0) then split0
    else if (word 0).val = 1 ∧ (word 1).val = 1 then 1 - 2 * split0 else 0
  else if ((word 0).val = 0 ∧ (word 1).val = 1) ∨ ((word 0).val = 1 ∧ (word 1).val = 0) then 1 / 2
    else 0

/-- Source Rot3c convention: cyclically shift the three mode profiles left. -/
def probability (rotation mode : Fin 3) (word : Fin 2 → Fin 3) : ℚ :=
  baseProbability (mode + rotation) word

def shape (rotation mode : Fin 3) : ℕ :=
  if (mode + rotation).val = 2 then 2 else 1

/-- PrepareShapes(2), in the actual release's lexicographic ordering. -/
def squareShapes : List (Fin 3 → ℕ) :=
  (List.range 5).flatMap fun i ↦
    (List.range (5 - i)).map fun j ↦ ![i, j, 4 - i - j]

def fourthShapes : List (Fin 3 → ℕ) :=
  (List.range 9).flatMap fun i ↦
    (List.range (9 - i)).map fun j ↦ ![i, j, 8 - i - j]

/-- Zero-based fourth shape position in global region one. -/
def firstPositiveParentPosition : ℕ :=
  fourthShapes.findIdx fun s ↦ ∀ mode, 0 < s mode

def parentShape : Fin 3 → ℕ := ![1, 1, 6]

/-- PrepareSplits for the first positive fourth consumer, without guessed IDs. -/
def parentSplits : List (Fin 3 → ℕ) :=
  squareShapes.filter fun s ↦ ∀ mode, s mode ≤ parentShape mode

/-- Preserve first occurrence when FindOrCreateTerm sees left then right. -/
def firstChildOrder : List (Fin 3 → ℕ) :=
  (parentSplits.flatMap fun s ↦ [s, fun mode ↦ parentShape mode - s mode]).foldl
    (fun acc s ↦ if s ∈ acc then acc else acc ++ [s]) []

/-- Exact IEEE rationals witnessing that the selected path is active in the
released candidate; these values are not asserted to form normalized parents. -/
def globalParentWeight : ℚ := 3033372711278953 / 4611686018427387904
def parentRegionWeight : ℚ := 6001991509460873 / 36028797018963968
def firstSplitWeight : ℚ := 2065402104995841 / 18014398509481984
def fourthSplitWeight : ℚ := 8261661794933301 / 72057594037927936

/-- Public DWZSquare shape indices for the actual 004/112 pair. -/
def publicPair : Fin 15 × Fin 15 := (0, 12)

end MME.MoreAsymmetryFirstSlice


