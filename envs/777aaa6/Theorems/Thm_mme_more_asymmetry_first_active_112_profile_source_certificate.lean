-- Prove2me | Theorems.Thm_mme_more_asymmetry_first_active_112_profile_source_certificate
-- name    : mme_more_asymmetry_first_active_112_profile_source_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:30:35.879056+00:00
-- url     : https://prove2.me/theorems/5ac52de5-a1f8-4984-982c-d9d93b9ff20a
-- title:
--   More Asymmetry: first active 112 profile and source-incidence certificate
-- statement:
--   For the released candidate's first active $(1,1,2)$ square consumer, all three cyclic transports of its exact rational complete profiles are nonnegative and normalized. Writing $\beta_{r,m}$ for rotation $r$ and mode $m$, and $s_{r,m}$ for the corresponding coordinate of the rotated shape, their support is exactly
--
--   $$\beta_{r,m}(a,b)\ne0\quad\Longleftrightarrow\quad a+b=s_{r,m},\qquad \sum_{a,b}\beta_{r,m}(a,b)=1.$$
--
--   The profiles therefore define genuine real complete-split probability profiles at level two. The finite source construction identifies the first positive fourth shape as $(1,1,6)$, at zero-based position10, and its first-occurrence child order as $004,112,013,103$. The four stored weights identifying the selected consumer path are strictly positive and $0<p<1/2$.
--
--   For every field, the canonical product of the $004$ and $112$ square blocks is a restriction of the canonical $116$ fourth block. This is the genuine source-tensor incidence used by the selected consumer.
--
--   This certificate proves local normalization, support and tensor incidence only. It does not assert that these mode marginals admit a particular joint word distribution, prove a profile-restricted tensor value, establish the full witness's feasibility, or improve omega by itself. The two nonzero rotations are transports of this chosen consumer, not assertions that independently optimized rotated consumers use the same scalar.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu and Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.4–3.6 (printed pp.14–15) for complete split profiles. Exact released numerical specialization: OSF https://osf.io/mw5ak/, code_matrix_mult.zip v1 SHA256 a88d211df0a82f0bba0a77ccbad9103064ebef08eea95613e5926a4f666260d8, member data/W1.00_2.371339.mat SHA256 783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. The profile formulas are src/evaluation/TermInfoLv2.m lines134–146,180; scalar params(923), registered as square term2, parent11/region1, group181. Static incidence follows src/utils/PrepareShapes.m, PrepareSplits.m, src/evaluation/FindOrCreateTerm.m and TermInfo.Build. This is a finite source-data specialization, not the paper's extraction or numerical omega theorem.

import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Theorems.Thm_mme_dwz_fourth_pair_factor_restrictions_to_coarse
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096

open BigOperators MME
open MME.MoreAsymmetryFirstSlice

universe u

theorem mme_more_asymmetry_first_active_112_profile_source_certificate :
    (0 < split0 ∧ split0 < 1 / 2) ∧
    (0 < globalParentWeight ∧ 0 < parentRegionWeight ∧
      0 < firstSplitWeight ∧ 0 < fourthSplitWeight) ∧
    (firstPositiveParentPosition = 10 ∧ fourthShapes[10]? = some parentShape) ∧
    (firstChildOrder = [![0, 0, 4], ![1, 1, 2], ![0, 1, 3], ![1, 0, 3]]) ∧
    (∀ rotation mode : Fin 3,
      (∀ word : Fin 2 → Fin 3, 0 ≤ probability rotation mode word) ∧
      (∑ word : Fin 2 → Fin 3, probability rotation mode word) = 1 ∧
      (∀ word : Fin 2 → Fin 3,
        probability rotation mode word ≠ 0 ↔
          (word 0).val + (word 1).val = shape rotation mode)) ∧
    ((DWZSquare.shapeX publicPair.1).val + (DWZSquare.shapeX publicPair.2).val = 1 ∧
      (DWZSquare.shapeY publicPair.1).val + (DWZSquare.shapeY publicPair.2).val = 1 ∧
      (DWZSquare.shapeZ publicPair.1).val + (DWZSquare.shapeZ publicPair.2).val = 6) ∧
    (∃ beta : Fin 3 → Fin 3 → CompleteSplit.Profile 2,
      ∀ rotation mode word,
        (beta rotation mode).probability word = (probability rotation mode word : ℝ)) ∧
    (∀ (K : Type u) [Field K],
      TensorObj.Restrict
        (TensorObj.kron
          ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 0 4))
          ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 1 1 2)))
        ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor ![1, 1, 6])) := by sorry
