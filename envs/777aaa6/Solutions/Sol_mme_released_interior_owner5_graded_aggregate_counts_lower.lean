-- Prove2me | solution 1 for mme_released_interior_owner5_graded_aggregate_counts_lower
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:28:32.746221+00:00
-- url     : https://prove2.me/submissions/26d93dd9-5a37-45d5-9ba6-f5e06eb6c0d8

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

private theorem aggregate_row_5_10 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 10 0 i →
      ((ReleasedGlobal.jointRows 5 10).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 10).region.getD r.val 0 *
      ∑ c : Split 10, splitWeight 5 10 r c *
        childMarginal 5 10 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 10 r (complement (parent_total 10 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_5_11 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 11 0 i →
      ((ReleasedGlobal.jointRows 5 11).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 11).region.getD r.val 0 *
      ∑ c : Split 11, splitWeight 5 11 r c *
        childMarginal 5 11 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 11 r (complement (parent_total 11 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_5_12 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 12 0 i →
      ((ReleasedGlobal.jointRows 5 12).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 12).region.getD r.val 0 *
      ∑ c : Split 12, splitWeight 5 12 r c *
        childMarginal 5 12 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 12 r (complement (parent_total 12 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_5_13 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 13 0 i →
      ((ReleasedGlobal.jointRows 5 13).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 13).region.getD r.val 0 *
      ∑ c : Split 13, splitWeight 5 13 r c *
        childMarginal 5 13 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 13 r (complement (parent_total 13 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_5_14 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 14 0 i →
      ((ReleasedGlobal.jointRows 5 14).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 14).region.getD r.val 0 *
      ∑ c : Split 14, splitWeight 5 14 r c *
        childMarginal 5 14 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 14 r (complement (parent_total 14 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_5_15 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 15 0 i →
      ((ReleasedGlobal.jointRows 5 15).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 15).region.getD r.val 0 *
      ∑ c : Split 15, splitWeight 5 15 r c *
        childMarginal 5 15 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 15 r (complement (parent_total 15 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_5_18 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 18 0 i →
      ((ReleasedGlobal.jointRows 5 18).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 18).region.getD r.val 0 *
      ∑ c : Split 18, splitWeight 5 18 r c *
        childMarginal 5 18 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 18 r (complement (parent_total 18 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_5_19 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 19 0 i →
      ((ReleasedGlobal.jointRows 5 19).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 19).region.getD r.val 0 *
      ∑ c : Split 19, splitWeight 5 19 r c *
        childMarginal 5 19 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 19 r (complement (parent_total 19 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_5_20 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 20 0 i →
      ((ReleasedGlobal.jointRows 5 20).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 20).region.getD r.val 0 *
      ∑ c : Split 20, splitWeight 5 20 r c *
        childMarginal 5 20 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 20 r (complement (parent_total 20 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_5_21 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 21 0 i →
      ((ReleasedGlobal.jointRows 5 21).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 21).region.getD r.val 0 *
      ∑ c : Split 21, splitWeight 5 21 r c *
        childMarginal 5 21 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 21 r (complement (parent_total 21 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_5_22 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 22 0 i →
      ((ReleasedGlobal.jointRows 5 22).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 22).region.getD r.val 0 *
      ∑ c : Split 22, splitWeight 5 22 r c *
        childMarginal 5 22 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 22 r (complement (parent_total 22 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

theorem solution (s : Fin 45) :
    s.val < 25 →
    (seed 5 s).boundary = [] →
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent s 0 i →
      ((ReleasedGlobal.jointRows 5 s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight 5 s r c *
        childMarginal 5 s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  fin_cases s
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact fun _ _ => aggregate_row_5_10
  · exact fun _ _ => aggregate_row_5_11
  · exact fun _ _ => aggregate_row_5_12
  · exact fun _ _ => aggregate_row_5_13
  · exact fun _ _ => aggregate_row_5_14
  · exact fun _ _ => aggregate_row_5_15
  · decide +kernel
  · decide +kernel
  · exact fun _ _ => aggregate_row_5_18
  · exact fun _ _ => aggregate_row_5_19
  · exact fun _ _ => aggregate_row_5_20
  · exact fun _ _ => aggregate_row_5_21
  · exact fun _ _ => aggregate_row_5_22
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms solution
