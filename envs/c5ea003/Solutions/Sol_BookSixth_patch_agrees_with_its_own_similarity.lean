-- Prove2me | solution 1 for BookSixth.patch_agrees_with_its_own_similarity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T20:57:18.737502+00:00
-- url     : https://prove2.me/submissions/e25c88a7-e485-461d-a915-35832bd85e57

import Mathlib
import Definitions.Def_BookSixth

noncomputable section

open scoped BigOperators
open BookSixth

/-- **The cut-off patch collapses to the `i`-th similarity wherever the cut-offs
separate.**

The patched displacement `x ↦ x + ∑ j, chi j x • (S j x - x)` is anisotropic
away from the components in general, but at any point `x` where `chi i x = 1`
and every other cut-off vanishes, the sum has exactly one surviving summand and
the whole expression collapses to `S i x`.

This is the hinge of the roundness argument. It is what makes the ambient map's
anisotropy irrelevant: the Proved theorem
`BookSixth.localized_similarity_isotopy_keeps_roundness` (f90b81d4) needs only
agreement of the ambient map with a similarity *on the component itself*, not
on all of space, and this lemma supplies that agreement term by term. -/
theorem solution {n : ℕ} (i : Fin n)
    (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3) (x : Space3)
    (hone : chi i x = 1) (hzero : ∀ j ∈ Finset.univ, j ≠ i → chi j x = 0) :
    x + ∑ j, chi j x • (S j x - x) = S i x := by
  classical
  have hsum : ∑ j : Fin n, chi j x • (S j x - x) = 1 • (S i x - x) := by
    calc (∑ j : Fin n, chi j x • (S j x - x))
        = ∑ j : Fin n, if j = i then chi j x • (S j x - x) else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hji : j = i
          · simp [hji]
          · rw [if_neg hji, hzero j (Finset.mem_univ j) hji, zero_smul]
      _ = 1 • (S i x - x) := by simp [hone]
  rw [hsum, one_smul]
  abel
