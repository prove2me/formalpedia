-- Prove2me | solution 1 for TropicalLA.pathWeight_excise
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:18:59.94391+00:00
-- url     : https://prove2.me/submissions/8964ae6f-1ee5-46ed-a16b-33894ff60d9c

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA Finset in
theorem solution {ι : Type*} (A : Matrix ι ι ℝ) (p : ℕ → ι) {a b m : ℕ}
    (hab : a < b) (hbm : b ≤ m) (hp : p a = p b) :
    pathWeight A (fun t => if t < a then p t else p (t + (b - a))) (m - (b - a))
      + pathWeight A (fun t => p (a + t)) (b - a) = pathWeight A p m := by
  set q : ℕ → ι := fun t => if t < a then p t else p (t + (b - a)) with hq
  unfold pathWeight
  -- split `[0, m)` as `[0, a) ∪ [a, b) ∪ [b, m)`, and the excised walk as `[0, a) ∪ [a, a + (m - b))`
  have h1 : m - (b - a) = a + (m - b) := by omega
  have h2 : m = a + ((b - a) + (m - b)) := by omega
  rw [h1, sum_range_add]
  conv_rhs => rw [h2, sum_range_add, sum_range_add]
  -- before the loop, the excised walk agrees with `p` (at `t = a - 1` it jumps to `p b = p a`)
  have hfirst : ∑ t ∈ range a, A (q t) (q (t + 1)) = ∑ t ∈ range a, A (p t) (p (t + 1)) := by
    refine sum_congr rfl fun t ht => ?_
    rw [mem_range] at ht
    have hqt : q t = p t := by simp only [hq, if_pos ht]
    have hqt1 : q (t + 1) = p (t + 1) := by
      by_cases h : t + 1 < a
      · simp only [hq, if_pos h]
      · have : t + 1 = a := by omega
        simp only [hq, if_neg h]
        rw [this, show a + (b - a) = b by omega, ← hp]
    rw [hqt, hqt1]
  -- after the loop, it is `p` shifted by the loop length
  have hlast : ∑ k ∈ range (m - b), A (q (a + k)) (q (a + k + 1))
      = ∑ k ∈ range (m - b), A (p (a + ((b - a) + k))) (p (a + ((b - a) + k) + 1)) := by
    refine sum_congr rfl fun k _ => ?_
    have e1 : q (a + k) = p (a + ((b - a) + k)) := by
      simp only [hq, if_neg (by omega : ¬ a + k < a)]
      congr 1
      omega
    have e2 : q (a + k + 1) = p (a + ((b - a) + k) + 1) := by
      simp only [hq, if_neg (by omega : ¬ a + k + 1 < a)]
      congr 1
      omega
    rw [e1, e2]
  simp only [add_assoc] at hfirst hlast ⊢
  rw [hfirst, hlast]
  ring
