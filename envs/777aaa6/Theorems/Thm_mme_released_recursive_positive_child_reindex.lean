-- Prove2me | Theorems.Thm_mme_released_recursive_positive_child_reindex
-- name    : mme_released_recursive_positive_child_reindex
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T04:19:53.858074+00:00
-- url     : https://prove2.me/theorems/ed9c702e-1a3f-4ba8-83b6-54fe14405e7b
-- title:
--   Exact pooling of the released positive recursive children
-- statement:
--   The positive children of the six released level-three regions are in bijection with the 1,104 rows of the pooled level-two table. A positive child consists of a region $\rho$, one of its 88 parent rows and an admissible split whose three grades and total child mass are all positive. If $c_r$ is the child corresponding to pooled row $r$, the bijection preserves the physical parent grades, integer mass and split parameter. Physical mode $i$ is regional mode $\sigma_\rho^{-1}(i)$ under the canonical role permutation.
--
--   Let $D=10^{12}$, let $H(c)$ be the sum of the split masses of $c$ and its complement, and write $N_r=\operatorname{n2}(r)$. For every pooled row, $N_r=H(c_r)$. For every mode $i$ and complete two-letter word $(u,v)$,
--
--   $$
--   D\,\mu^{(3)}_{\rho,\sigma_\rho^{-1}(i)}(c_r,(u,v))
--   =N_r\,\mathbf{1}_{\{v=\operatorname{parent2}(r,i)-u\}}J_m(r,i,u).
--   $$
--
--   Here the subtraction is the natural-number subtraction used by the canonical marginal formula. Thus the bijection preserves all nine integer word weights in each mode, not only total masses or the three central grade vectors. This is a finite data bridge for the recursive continuation; it makes no claim about the final extraction rate or matrix volume.
-- source:
--   Finite reindexing of marwahaha's [released recursive data](p2m:theorem/60610bd3-0675-4be4-a731-ca71c173a5bc) and [level-two split data](p2m:theorem/5b17d80e-d6d1-4f7d-9eb0-6ee1a393acd6). It uses the [canonical closed marginal theorem](p2m:theorem/75a0e5d2-aa1a-4524-a4d3-d71a13406e4a), proved in [submission b15db355](p2m:solution/b15db355-66be-4f91-933f-84549689120f), and the [shape and parameter bounds](p2m:theorem/1a74fd3d-dc7d-4605-80a2-8764ba5233f4). The recursive extraction framework follows Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6. This statement connects two formal data presentations; it is not a new exponent bound.

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_joint_interior_profiles

set_option autoImplicit false
open MME MME.RecursiveYZ MME.CompleteSplit

theorem mme_released_recursive_positive_child_reindex :
    ∃ reindex : Fin 1104 ≃
      {cell : (region : Fin 6) × Cell 4 88 (RecStage.parent3 region) //
        (∀ i : Fin 3, 0 < (cell.2.2.val i).val) ∧
        0 < RecStage.m3 cell.1 cell.2.1 cell.2.2 +
          RecStage.m3 cell.1 cell.2.1
            (complement (RecStage.htotal3 cell.1 cell.2.1) cell.2.2)},
      ∀ row : Fin 1104,
        (∀ i : Fin 3, RecStage.parent2 row i =
          ((reindex row).val.2.2.val
            ((ReleasedJointInterior.roleEquiv (reindex row).val.1).symm i)).val) ∧
        RecStage.n2 row =
          RecStage.m3 (reindex row).val.1 (reindex row).val.2.1 (reindex row).val.2.2 +
          RecStage.m3 (reindex row).val.1 (reindex row).val.2.1
            (complement (RecStage.htotal3 (reindex row).val.1 (reindex row).val.2.1)
              (reindex row).val.2.2) ∧
        (RecStage.l2At row).2.2 =
          (RecStage.cellRec (reindex row).val.1 (reindex row).val.2.1
            (reindex row).val.2.2).2 ∧
        (∀ (i : Fin 3) (word : CompleteWord 2),
          RecStage.D * RecStage.mu3 (reindex row).val.1
            ((ReleasedJointInterior.roleEquiv (reindex row).val.1).symm i)
            (reindex row).val.2 word =
          RecStage.n2 row *
            (if (word 1).val = RecStage.parent2 row i - (word 0).val then
              L2Cert.Jm row i (word 0) else 0)) := by sorry
