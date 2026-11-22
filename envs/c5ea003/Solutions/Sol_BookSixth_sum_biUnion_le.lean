-- Prove2me | solution 1 for BookSixth.sum_biUnion_le
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-16T15:20:47.322329+00:00
-- url     : https://prove2.me/submissions/59edd3c4-8f23-4578-b2ec-166371e66f35

import Mathlib
import Definitions.Def_BookSixth

set_option autoImplicit false

theorem solution (I A : Type) [DecidableEq I] [DecidableEq A]
    (s : Finset I) (t : I -> Finset A) (w : A -> Real)
    (hw : forall a, LE.le 0 (w a)) :
    LE.le (Finset.sum (s.biUnion t) w) (Finset.sum s (fun i => Finset.sum (t i) w)) := by
  have htwo : forall (U V : Finset A),
      LE.le (Finset.sum (U ∪ V) w) ((Finset.sum U w) + Finset.sum V w) := by
    intro U V
    have hunion : U ∪ V = ((V \ U) ∪ U) := by
      rw [Finset.sdiff_union_self_eq_union, Finset.union_comm]
    have hdis : Disjoint ((V \ U)) U := (Finset.disjoint_sdiff (s := U) (t := V)).symm
    calc Finset.sum (U ∪ V) w
        = Finset.sum (((V \ U)) ∪ U) w := by rw [hunion]
      _ = (Finset.sum ((V \ U)) w) + Finset.sum U w :=
        Finset.sum_union hdis
      _ ≤ (Finset.sum V w) + Finset.sum U w :=
        add_le_add_left
          (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun x _ _ => hw x)) _
      _ = (Finset.sum U w) + Finset.sum V w := by rw [add_comm]
  induction s using Finset.induction with
  | empty =>
    simp
  | @insert a s has ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert has]
    calc Finset.sum ((t a) ∪ (s.biUnion t)) w
        ≤ (Finset.sum (t a) w) + Finset.sum (s.biUnion t) w := htwo _ _
      _ ≤ (Finset.sum (t a) w) + Finset.sum s (fun i => Finset.sum (t i) w) :=
        add_le_add_right ih _
