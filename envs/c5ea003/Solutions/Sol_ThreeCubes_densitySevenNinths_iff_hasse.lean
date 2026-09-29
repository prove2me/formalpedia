-- Prove2me | solution 1 for ThreeCubes.densitySevenNinths_iff_hasse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:56:10.236212+00:00
-- url     : https://prove2.me/submissions/ff2e65e0-884c-4129-8a4b-15b77d7af4b3

-- Sol generated from Probability/Density.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_Density
import Theorems.Thm_ThreeCubes_card_admissible_block
import Theorems.Thm_ThreeCubes_locallySolvable_iff
import Theorems.Thm_ThreeCubes_locallySolvable_of_isSumOfThreeCubes
import Theorems.Thm_ThreeCubes_locallySolvable_of_not_mod_nine

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


open scoped Classical in
/-- **The locally solvable integers have density exactly `7/9`.** -/
theorem card_locallySolvable_block (N : ℕ) :
    (Finset.filter (fun i : ℕ => LocallySolvable (i : ℤ)) (Finset.range (9 * N))).card = 7 * N := by
  rw [show Finset.filter (fun i : ℕ => LocallySolvable (i : ℤ)) (Finset.range (9 * N))
      = (Finset.range (9 * N)).filter (fun i => i % 9 ≠ 4 ∧ i % 9 ≠ 5) from ?_]
  · exact card_admissible_block N
  · ext x
    simp only [Finset.mem_filter, Finset.mem_range, locallySolvable_iff]
    omega





open ThreeCubes in
open scoped Classical in
theorem solution:
    DensitySevenNinths ↔ ∀ n : ℕ, (n : ℤ) % 9 ≠ 4 → (n : ℤ) % 9 ≠ 5 →
      IsSumOfThreeCubes (n : ℤ) := by
  constructor
  · intro hD n h4 h5
    -- consider the block containing `n`
    have hlt : n < 9 * (n + 1) := by omega
    have hcard := hD (n + 1)
    have hsub : Finset.filter (fun i : ℕ => IsSumOfThreeCubes (i : ℤ)) (Finset.range (9 * (n + 1))) ⊆
        Finset.filter (fun i : ℕ => LocallySolvable (i : ℤ)) (Finset.range (9 * (n + 1))) := by
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, locallySolvable_of_isSumOfThreeCubes hx.2⟩
    have heq : Finset.filter (fun i : ℕ => IsSumOfThreeCubes (i : ℤ)) (Finset.range (9 * (n + 1))) =
        Finset.filter (fun i : ℕ => LocallySolvable (i : ℤ)) (Finset.range (9 * (n + 1))) := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [card_locallySolvable_block (n + 1), hcard]
    have hmem : n ∈ Finset.filter (fun i : ℕ => LocallySolvable (i : ℤ)) (Finset.range (9 * (n + 1))) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hlt, locallySolvable_of_not_mod_nine h4 h5⟩
    rw [← heq] at hmem
    simp only [Finset.mem_filter] at hmem
    exact hmem.2
  · intro hH N
    rw [← card_locallySolvable_block N]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, locallySolvable_of_isSumOfThreeCubes h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨h4, h5⟩ := (locallySolvable_iff _).mp h2
      exact ⟨h1, hH x h4 h5⟩
