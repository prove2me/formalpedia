-- Prove2me | Theorems.Thm_mme_released_positive_region2_profile_reindex
-- name    : mme_released_positive_region2_profile_reindex
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T00:56:17.20054+00:00
-- url     : https://prove2.me/theorems/25a9f718-522b-414e-ab36-f6d0a7b48f7c
-- title:
--   Positive profile reindexing for recursive region 2
-- statement:
--   Fix the published exact data for recursive region 2. Write $P(j)$, $N(k,j)$, $M(k,j,c)$, and $U(k,i,j,c,w)$ for the parent grade, block count, split count, and complete-word marginal count in `ReleasedJointInterior`. Here $j\in\{0,\ldots,269\}$ indexes an outer owner and an actual parent shape. Define its positive labels by
--
--   $$
--   I=\{j:N(1,j)>0\}.
--   $$
--
--   Write $p_3(r)$, $n_3(r)$, $m_3(r,c)$, and $\mu_3(i,r,c,w)$ for the corresponding compact region-2 data in `RecStage`, where $r\in\{0,\ldots,87\}$.
--
--   There is a bijection $e:\{0,\ldots,87\}\to I$ that preserves parent grades and, for every natural-number scale $k$, satisfies
--
--   $$
--   P(e(r))=p_3(r),\qquad N(k,e(r))=k\,n_3(r),
--   $$
--
--   $$
--   M(k,e(r),c)=k\,m_3(r,c),\qquad U(k,i,e(r),c,w)=k\,\mu_3(i,r,c,w).
--   $$
--
--   The last two identities hold for every child grade $c=(c_0,c_1,c_2)$ with $c_0+c_1+c_2=4$ and $c_i\le p_3(r)_i$, every mode $i\in\{0,1,2\}$, and every two-letter word $w\in\{0,1,2\}^2$. The equality of parent grades transports $c$ without changing its coordinates. The bijection uses positivity at unit scale, and the count identities include $k=0$.
-- source:
--   Auxiliary exact-data identity between the canonical definitions mme_released_recursive_stage_data (60610bd3-0675-4be4-a731-ca71c173a5bc, marwahaha) and mme_released_joint_interior_profiles (3d489536-019f-46c1-b6c3-52ee24f948d0, Robertboy18), using the released exact seed (cb80ec03-0b0a-4b6c-a75e-ca788b94d914, raresbuhai). Underlying construction: Alman, Duan, Vassilevska Williams, Xu, Xu and Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/pdf/2404.16349v2, Section 6.1 and Claim 6.5, printed page 32, together with the released parameters. The present statement identifies two published formal interfaces and is not a theorem stated verbatim in the paper.

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_profiles

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MME MME.RecursiveYZ

theorem mme_released_positive_region2_profile_reindex :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 2 1 j})
      (hparent : ∀ r, RecStage.parent3 2 r = ReleasedJointInterior.parent 2 (e r).val),
      ∀ k : ℕ,
        (∀ r, ReleasedJointInterior.size 2 k (e r).val = k * RecStage.n3 2 r) ∧
        (∀ (r : Fin 88) (c : RecursiveThinSplit.Split 4 (RecStage.parent3 2 r)),
          ReleasedJointInterior.splitCount 2 k (e r).val
            (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c) =
              k * RecStage.m3 2 r c) ∧
        (∀ (i : Fin 3) (r : Fin 88)
          (c : RecursiveThinSplit.Split 4 (RecStage.parent3 2 r))
          (w : CompleteSplit.CompleteWord 2),
          ReleasedJointInterior.integerProfile 2 k i
            ⟨(e r).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c⟩ w =
              k * RecStage.mu3 2 i ⟨r, c⟩ w) := by sorry
