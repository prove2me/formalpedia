-- Prove2me | solution 1 for mme_released_interior_owner4_graded_aggregate_counts_upper
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:32:06.612955+00:00
-- url     : https://prove2.me/submissions/3f0907d5-f0d9-4e59-939a-c0db0b3fc21f

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

private theorem aggregate_row_4_25 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 25 0 i →
      ((ReleasedGlobal.jointRows 4 25).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 25).region.getD r.val 0 *
      ∑ c : Split 25, splitWeight 4 25 r c *
        childMarginal 4 25 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 25 r (complement (parent_total 25 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_4_26 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 26 0 i →
      ((ReleasedGlobal.jointRows 4 26).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 26).region.getD r.val 0 *
      ∑ c : Split 26, splitWeight 4 26 r c *
        childMarginal 4 26 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 26 r (complement (parent_total 26 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_4_27 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 27 0 i →
      ((ReleasedGlobal.jointRows 4 27).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 27).region.getD r.val 0 *
      ∑ c : Split 27, splitWeight 4 27 r c *
        childMarginal 4 27 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 27 r (complement (parent_total 27 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_4_28 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 28 0 i →
      ((ReleasedGlobal.jointRows 4 28).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 28).region.getD r.val 0 *
      ∑ c : Split 28, splitWeight 4 28 r c *
        childMarginal 4 28 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 28 r (complement (parent_total 28 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_4_31 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 31 0 i →
      ((ReleasedGlobal.jointRows 4 31).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 31).region.getD r.val 0 *
      ∑ c : Split 31, splitWeight 4 31 r c *
        childMarginal 4 31 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 31 r (complement (parent_total 31 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_4_32 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 32 0 i →
      ((ReleasedGlobal.jointRows 4 32).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 32).region.getD r.val 0 *
      ∑ c : Split 32, splitWeight 4 32 r c *
        childMarginal 4 32 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 32 r (complement (parent_total 32 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_4_33 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 33 0 i →
      ((ReleasedGlobal.jointRows 4 33).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 33).region.getD r.val 0 *
      ∑ c : Split 33, splitWeight 4 33 r c *
        childMarginal 4 33 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 33 r (complement (parent_total 33 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_4_36 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 36 0 i →
      ((ReleasedGlobal.jointRows 4 36).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 36).region.getD r.val 0 *
      ∑ c : Split 36, splitWeight 4 36 r c *
        childMarginal 4 36 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 36 r (complement (parent_total 36 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_4_37 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 37 0 i →
      ((ReleasedGlobal.jointRows 4 37).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 37).region.getD r.val 0 *
      ∑ c : Split 37, splitWeight 4 37 r c *
        childMarginal 4 37 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 37 r (complement (parent_total 37 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

private theorem aggregate_row_4_40 :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent 40 0 i →
      ((ReleasedGlobal.jointRows 4 40).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 40).region.getD r.val 0 *
      ∑ c : Split 40, splitWeight 4 40 r c *
        childMarginal 4 40 r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 40 r (complement (parent_total 40 r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

theorem solution (s : Fin 45) :
    25 ≤ s.val →
    (seed 4 s).boundary = [] →
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent s 0 i →
      ((ReleasedGlobal.jointRows 4 s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight 4 s r c *
        childMarginal 4 s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 s r (complement (parent_total s r) c) i
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
  · exact fun _ _ => aggregate_row_4_25
  · exact fun _ _ => aggregate_row_4_26
  · exact fun _ _ => aggregate_row_4_27
  · exact fun _ _ => aggregate_row_4_28
  · decide +kernel
  · decide +kernel
  · exact fun _ _ => aggregate_row_4_31
  · exact fun _ _ => aggregate_row_4_32
  · exact fun _ _ => aggregate_row_4_33
  · decide +kernel
  · decide +kernel
  · exact fun _ _ => aggregate_row_4_36
  · exact fun _ _ => aggregate_row_4_37
  · decide +kernel
  · decide +kernel
  · exact fun _ _ => aggregate_row_4_40
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms solution
