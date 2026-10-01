-- Prove2me | Theorems.Thm_mme_released_joint_positive_source_inclusion
-- name    : mme_released_joint_positive_source_inclusion
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T03:30:46.494971+00:00
-- url     : https://prove2.me/theorems/0f51d84d-2e85-4c2a-bf5b-88ab793e7c41
-- title:
--   Common parent-graded regional sources enter the positive global window
-- statement:
--   For every positive natural scale $k$ and every family $a_o$ of released global reference addresses, there is an equivalence
--   $$E:\coprod_{r=0}^{5}\operatorname{Fin}(4B_r(k))\simeq\operatorname{Fin}(\operatorname{partSize}(k,a,1)),$$
--   where $B_r(k)$ is the number of parent blocks in common inner region $r$, and the right side enumerates the positive part of the global two-part split.
--
--   The same equivalence works for every common tolerance $\eta>0$, every owner tolerance family $\varepsilon$ with $\eta\leq\varepsilon_o$ for all owners, every physical mode $i$, and every fine word $y$ on the positive part. Suppose the word pulled back to each region through $E$ has its prescribed parent grades and lies in the ordinary common parent-typical band of tolerance $\eta$, read in regional mode $\operatorname{roleEquiv}(r)^{-1}(i)$. Then $y$ satisfies `QPos k a eps i`.
--
--   Thus every positive global block has its prescribed grade, and each owner/shape fiber has the released four-letter word frequencies within $\varepsilon_o$, normalized by the total number of blocks of owner $o$. The reference addresses are arbitrary, and the position equivalence is chosen before the tolerances, mode, and word. Zero-weight owner/shape fibers remain empty; no child-address grading or prescribed-histogram witness is assumed.
-- source:
--   Finite source-assembly interface for marwahaha's arbitrary-reference global two-part split (p2m:theorem/2e4d8b71-3338-40d7-a61d-3968afda52d7 and p2m:theorem/3d1878b8-2962-4d1b-a7af-7d9d333ef441), Robertboy18's common owner profiles and coordinate partition (p2m:theorem/64c0d922-1ef6-4773-ac11-bd3df00f1fdc, p2m:theorem/cdc6a5ae-7870-4e72-a534-412be10de951, and p2m:theorem/b358bb80-f9e9-49bc-b783-0ef996955884), and BrunoDCDO's parent-graded cell-window theorem (p2m:theorem/464f6f2b-efd1-48d0-9e63-96ffb0545e1e). The exact released data originate in raresbuhai's seed. The regional decomposition follows Alman, Duan, Vassilevska Williams, Yinzhan Xu, Zixuan Xu and Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6.SS1, Section 6.1 and Claim 6.5. This finite interface is not stated verbatim in the paper and supplies a source obligation for p2m:theorem/55bde106-3adc-41ac-bbd9-8e89d799a028.

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_released_joint_interior_position_data
import Definitions.Def_mme_graded_integer_regional_step_data
set_option autoImplicit false
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit

theorem mme_released_joint_positive_source_inclusion (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, ReleasedGlobal.Reference o k) :
    ∃ E : (Σ r : Fin 6, Fin (ReleasedJointInterior.blocks r k * 4)) ≃
        Fin (ReleasedRecursive.Asm.partSize k a 1),
      ∀ (eta : ℝ), 0 < eta →
        ∀ (eps : Fin 6 → ℝ), (∀ o, eta ≤ eps o) →
          ∀ (i : Fin 3)
            (y : ProfiledCW.FineWord (ReleasedRecursive.Asm.partSize k a 1)),
            (∀ r,
              ParentGraded (ReleasedJointInterior.parent r) (ReleasedJointInterior.size r k)
                ((ReleasedJointInterior.roleEquiv r).symm i)
                (ProfiledCW.split (ell := 2) (ReleasedJointInterior.positions r k)
                  (ReleasedJointInterior.positions_length r k) (fun q => y (E ⟨r, q⟩))) ∧
              ReleasedJointInterior.source r k eta
                ((ReleasedJointInterior.roleEquiv r).symm i) (fun q => y (E ⟨r, q⟩))) →
              ReleasedRecursive.Asm.QPos k a eps i y := by sorry
