-- Prove2me | solution 1 for TropicalElimination.mem_tropVanishing_iff_min_attained_twice
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T04:39:37.871749+00:00
-- url     : https://prove2.me/submissions/447d0f07-05d0-4f0e-971a-8a200327ba84

import Mathlib
import Definitions.Def_Tropical_TropicalLinearSpaceElimination
open TropicalElimination in
theorem solution {E : Type*} [Nontrivial E] [Fintype E] [Nonempty E] (c : E → TT) (x : E → TT) :
    x ∈ tropVanishing c ↔
      ∃ i j, i ≠ j ∧ (∀ k, c i + x i ≤ c k + x k) ∧ c j + x j = c i + x i := by
  constructor
  · -- take a minimiser `i`; its witness `j` must tie with it
    intro hx
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun k => c k + x k)
      Finset.univ_nonempty
    obtain ⟨j, hji, hj⟩ := hx i
    exact ⟨i, j, fun h => hji h.symm, fun k => hi k (Finset.mem_univ k),
      le_antisymm hj (hi j (Finset.mem_univ j))⟩
  · -- the minimiser witnesses every other coordinate, and the tie witnesses the minimiser
    rintro ⟨i, j, hij, hmin, htie⟩ k
    by_cases hk : k = i
    · subst hk
      exact ⟨j, fun h => hij h.symm, htie.le⟩
    · exact ⟨i, fun h => hk h.symm, hmin k⟩
