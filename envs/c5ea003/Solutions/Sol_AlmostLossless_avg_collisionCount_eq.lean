-- Prove2me | solution 1 for AlmostLossless.avg_collisionCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T13:30:16.847029+00:00
-- url     : https://prove2.me/submissions/1c4e4b24-42eb-4789-af11-992cc5602489

import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Instances
open AlmostLossless in
theorem solution {S A M : Type*} [DecidableEq S] [DecidableEq M] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype M] [Nonempty M] {h : A → S → M} (hpi : PairwiseIndependent h)
    (T : Finset S) (x : S) :
    (∑ a : A, (collisionCount h T a x : ℚ)) / (Fintype.card A : ℚ)
      = ((T.erase x).card : ℚ) / (Fintype.card M : ℚ) := by
  have hsumN : (∑ a : A, ((T.erase x).filter (fun y => h a y = h a x)).card)
      * Fintype.card M = (T.erase x).card * Fintype.card A := by
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset A)) (t := T.erase x) (r := fun a y => h a y = h a x)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
    rw [hdc, Finset.sum_mul]
    calc ∑ y ∈ T.erase x, (Finset.univ.filter (fun a => h a y = h a x)).card * Fintype.card M
        = ∑ _y ∈ T.erase x, Fintype.card A := by
          refine Finset.sum_congr rfl (fun y hy => ?_)
          exact hpi y x (Finset.ne_of_mem_erase hy)
      _ = (T.erase x).card * Fintype.card A := by simp
  have hA : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℚ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
  have hsumQ : (∑ a : A, (collisionCount h T a x : ℚ)) * Fintype.card M
      = ((T.erase x).card : ℚ) * Fintype.card A := by
    unfold collisionCount
    rw [← Nat.cast_sum]
    exact_mod_cast hsumN
  rw [div_eq_div_iff hA.ne' hM.ne']
  linarith
