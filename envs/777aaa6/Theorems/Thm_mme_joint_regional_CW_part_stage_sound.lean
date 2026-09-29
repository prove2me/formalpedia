-- Prove2me | Theorems.Thm_mme_joint_regional_CW_part_stage_sound
-- name    : mme_joint_regional_CW_part_stage_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T00:51:39.167869+00:00
-- url     : https://prove2.me/theorems/916e4092-eb3a-4fc3-b051-c96ac27bb6ac
-- title:
--   Soundness of one oriented part stage
-- statement:
--   A part stage is one exact-type hashing step on the positions of a single part. It carries the part's source predicate $S$ to a target predicate $T$ using `types` exact steps, each yielding at least `copies` copies of its output. The outputs lie inside $T$ and cover every supported word that $T$ allows, each exactly once. A part stage may be reoriented by the cyclic or transposition mode permutations.
--
--   For every part stage, `copies` copies of the $T$-projection of $CW_5^{\otimes M}$ are a restriction of `types` copies of its $S$-projection.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: Theorem 5.3 (the global stage outputs one interface tensor over all six regions), Theorem 6.4 and Section 6.6 (each constituent stage divides every term into six regions, hashes each region jointly over all terms, and takes the tensor product of the six outputs), and Algorithm 1 in Section 7. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_joint_regional_CW_plan_data
open MME MME.TensorObj MME.ProfiledCW
set_option autoImplicit false
universe u

theorem mme_joint_regional_CW_part_stage_sound {K : Type u} [Field K] {M lower : ℕ} {S T : Predicate M}
    (D : PartStage M lower S T) :
    TensorObj.Restrict (bigAdd (fun _ : Fin D.copies ↦ tensor K T))
      (bigAdd (fun _ : Fin D.types ↦ tensor K S)) := by sorry
