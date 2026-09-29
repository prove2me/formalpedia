-- Prove2me | solution 1 for mme_released_interior_owner0_graded_aggregate_counts_upper
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:33:37.8265+00:00
-- url     : https://prove2.me/submissions/3c81eeda-cb50-4abf-9551-e540218c2ffb

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

private theorem aggregate_row_0_25 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 25 0 i →
      ((ReleasedGlobal.jointRows 0 25).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 25).region.getD r.val 0 *
      ∑ c : Split 25, splitWeight 0 25 r c *
        childMarginal 0 25 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 25 r (complement (parent_total 25 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_0_26 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 26 0 i →
      ((ReleasedGlobal.jointRows 0 26).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 26).region.getD r.val 0 *
      ∑ c : Split 26, splitWeight 0 26 r c *
        childMarginal 0 26 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 26 r (complement (parent_total 26 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_0_27 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 27 0 i →
      ((ReleasedGlobal.jointRows 0 27).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 27).region.getD r.val 0 *
      ∑ c : Split 27, splitWeight 0 27 r c *
        childMarginal 0 27 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 27 r (complement (parent_total 27 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_0_28 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 28 0 i →
      ((ReleasedGlobal.jointRows 0 28).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 28).region.getD r.val 0 *
      ∑ c : Split 28, splitWeight 0 28 r c *
        childMarginal 0 28 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 28 r (complement (parent_total 28 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_0_31 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 31 0 i →
      ((ReleasedGlobal.jointRows 0 31).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 31).region.getD r.val 0 *
      ∑ c : Split 31, splitWeight 0 31 r c *
        childMarginal 0 31 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 31 r (complement (parent_total 31 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_0_32 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 32 0 i →
      ((ReleasedGlobal.jointRows 0 32).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 32).region.getD r.val 0 *
      ∑ c : Split 32, splitWeight 0 32 r c *
        childMarginal 0 32 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 32 r (complement (parent_total 32 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_0_33 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 33 0 i →
      ((ReleasedGlobal.jointRows 0 33).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 33).region.getD r.val 0 *
      ∑ c : Split 33, splitWeight 0 33 r c *
        childMarginal 0 33 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 33 r (complement (parent_total 33 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_0_36 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 36 0 i →
      ((ReleasedGlobal.jointRows 0 36).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 36).region.getD r.val 0 *
      ∑ c : Split 36, splitWeight 0 36 r c *
        childMarginal 0 36 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 36 r (complement (parent_total 36 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_0_37 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 37 0 i →
      ((ReleasedGlobal.jointRows 0 37).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 37).region.getD r.val 0 *
      ∑ c : Split 37, splitWeight 0 37 r c *
        childMarginal 0 37 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 37 r (complement (parent_total 37 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_0_40 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 40 0 i →
      ((ReleasedGlobal.jointRows 0 40).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 40).region.getD r.val 0 *
      ∑ c : Split 40, splitWeight 0 40 r c *
        childMarginal 0 40 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 40 r (complement (parent_total 40 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

theorem solution (s : Fin 45) :
    25 ≤ s.val →
    (seed 0 s).boundary = [] →
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent s 0 i →
      ((ReleasedGlobal.jointRows 0 s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight 0 s r c *
        childMarginal 0 s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 s r (complement (parent_total s r) c) i
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
  · exact fun _ _ => aggregate_row_0_25
  · exact fun _ _ => aggregate_row_0_26
  · exact fun _ _ => aggregate_row_0_27
  · exact fun _ _ => aggregate_row_0_28
  · decide +kernel
  · decide +kernel
  · exact fun _ _ => aggregate_row_0_31
  · exact fun _ _ => aggregate_row_0_32
  · exact fun _ _ => aggregate_row_0_33
  · decide +kernel
  · decide +kernel
  · exact fun _ _ => aggregate_row_0_36
  · exact fun _ _ => aggregate_row_0_37
  · decide +kernel
  · decide +kernel
  · exact fun _ _ => aggregate_row_0_40
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms solution
