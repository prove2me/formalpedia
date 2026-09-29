-- Prove2me | solution 1 for mme_dwz_step2_broken_copy_aggregate_seven_eighths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:31:30.997042+00:00
-- url     : https://prove2.me/submissions/3a504ca8-4309-43ee-b010-77abb13f8a61

import Theorems.Thm_mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one
import Theorems.Thm_mme_finset_pointwise_one_eighth_aggregate_nonholes

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Block Outer Weight : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Outer] [DecidableEq Outer]
    [Fintype Weight] [DecidableEq Weight]
    (compatible useful : Block → Outer → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (hashRetained : Outer → Weight → Prop)
    [DecidableRel hashRetained]
    (retained : Outer)
    (hUseful : ∀ z : Block, useful z retained)
    (hCompatible : ∀ z : Block, compatible z retained)
    (hHash : ∀ w : Weight, hashRetained retained w)
    (hpointwise : ∀ z : Block,
      8 * (Finset.univ.filter (fun w : Weight ↦
        1 < (Finset.univ.filter (fun A : Outer ↦
          compatible z A ∧ hashRetained A w)).card)).card ≤
        Fintype.card Weight) :
    7 * Fintype.card Weight * Fintype.card Block ≤
      8 * ∑ w : Weight,
        (MME.DWZStep2.brokenCopy
          (fun z A ↦ compatible z A ∧ hashRetained A w)
          useful retained).nonholes.card := by
  classical
  let bad : Block → Weight → Prop := fun z w ↦
    1 < (Finset.univ.filter (fun A : Outer ↦
      compatible z A ∧ hashRetained A w)).card
  have hbad : ∀ z : Block,
      8 * (Finset.univ.filter (bad z)).card ≤ Fintype.card Weight := by
    simpa only [bad] using hpointwise
  have hmass :=
    mme_finset_pointwise_one_eighth_aggregate_nonholes bad hbad
  have hsets (w : Weight) :
      Finset.univ.filter (fun z : Block ↦ ¬ bad z w) =
        (MME.DWZStep2.brokenCopy
          (fun z A ↦ compatible z A ∧ hashRetained A w)
          useful retained).nonholes := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hiff := mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one
      compatible useful hashRetained z retained w
        (hUseful z) (hCompatible z) (hHash w)
    simpa only [bad, not_not] using (not_congr hiff).symm
  simpa only [hsets] using hmass
