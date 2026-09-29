-- Prove2me | solution 1 for ThreeCubes.card_admissible_block
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:22:44.861381+00:00
-- url     : https://prove2.me/submissions/5a1b3bed-9074-4bbf-af60-583d60ba0e57

-- Sol generated from Probability/Density.lean
import Mathlib
import Definitions.Def_Probability_Density

/-!
# Density of locally solvable and of representable integers

Combining the main local-solvability theorem with an exact count over each block of nine
consecutive integers we obtain:

* `ThreeCubes.card_locallySolvable_block` — exactly `7N` of the integers `0, …, 9N-1` are
  everywhere locally solvable, i.e. the locally solvable integers have density exactly `7/9`;
* `ThreeCubes.card_isSumOfThreeCubes_le` — consequently at most `7N` of them are actual sums
  of three cubes.  The conjecture of Heath-Brown asserts that this upper bound is attained
  (asymptotically), i.e. that the density of representable integers is exactly `7/9`; the
  formal statement `ThreeCubes.DensitySevenNinths` records that conjecture, and
  `ThreeCubes.densitySevenNinths_iff_hasse` shows it is *equivalent* to the Hasse principle
  for the affine cubic surface.
-/

open ThreeCubes

open Finset







open ThreeCubes in
theorem solution(N : ℕ) :
    ((Finset.range (9 * N)).filter (fun i => i % 9 ≠ 4 ∧ i % 9 ≠ 5)).card = 7 * N := by
  induction N with
  | zero => simp
  | succ M ih =>
      have h : 9 * (M + 1) = (9 * M) + 9 := by ring
      have hdisj : Disjoint (Finset.range (9 * M))
          (Finset.map (addLeftEmbedding (9 * M)) (Finset.range 9)) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        simp only [Finset.mem_range] at ha
        simp only [Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply] at hb
        obtain ⟨c, hc, rfl⟩ := hb
        omega
      rw [h, Finset.range_add, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj), ih,
        Finset.filter_map, Finset.card_map]
      have hc : Finset.filter ((fun i => i % 9 ≠ 4 ∧ i % 9 ≠ 5) ∘ ⇑(addLeftEmbedding (9 * M)))
          (Finset.range 9) = Finset.filter (fun i => i % 9 ≠ 4 ∧ i % 9 ≠ 5) (Finset.range 9) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply,
          addLeftEmbedding_apply]
        omega
      rw [hc]
      have h7 : (Finset.filter (fun i => i % 9 ≠ 4 ∧ i % 9 ≠ 5) (Finset.range 9)).card = 7 := by
        decide
      omega
