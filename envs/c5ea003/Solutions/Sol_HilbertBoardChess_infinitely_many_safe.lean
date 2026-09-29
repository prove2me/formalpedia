-- Prove2me | solution 1 for HilbertBoardChess.infinitely_many_safe
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:56:36.219441+00:00
-- url     : https://prove2.me/submissions/8e7c9ad5-ea57-4e6c-b04f-c93e7502c745

import Mathlib
import Definitions.Def_Applications_HilbertSpace_HilbertBoardChess
open HilbertBoardChess in
theorem solution {d : ℕ} (R : Finset (Sq d)) :
    {s : Sq d | ¬ attackedBy R s}.Infinite := by
  classical
  -- a bound on the first two coordinates of every rook
  set M : ℤ := ∑ r ∈ R, (|r 0| + |r 1|) with hM
  have hbound : ∀ r ∈ R, |r 0| ≤ M ∧ |r 1| ≤ M := by
    intro r hr
    have hle : |r 0| + |r 1| ≤ M :=
      Finset.single_le_sum (f := fun r : Sq d => |r 0| + |r 1|)
        (fun r _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hr
    exact ⟨by linarith [abs_nonneg (r 1)], by linarith [abs_nonneg (r 0)]⟩
  -- the constant squares beyond the bound differ from every rook in coordinates `0` and `1`
  let f : ℕ → Sq d := fun t _ => M + 1 + t
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrFun hab 0
    simp only [f] at this
    exact_mod_cast (by linarith : (a : ℤ) = b)
  have h01 : (0 : Fin (d + 2)) ≠ 1 := by simp [Fin.ext_iff]
  refine Set.infinite_of_injective_forall_mem hinj fun t => ?_
  rintro ⟨r, hr, -, j, hj⟩
  obtain ⟨hr0, hr1⟩ := hbound r hr
  have ht : (0 : ℤ) ≤ t := Int.natCast_nonneg t
  by_cases hj0 : (0 : Fin (d + 2)) = j
  · have h1 : f t 1 = r 1 := hj 1 (fun h => h01 (hj0.trans h.symm))
    simp only [f] at h1
    have := le_abs_self (r 1)
    linarith
  · have h0 : f t 0 = r 0 := hj 0 hj0
    simp only [f] at h0
    have := le_abs_self (r 0)
    linarith
