-- Prove2me | solution 1 for TropicalElimination.card_support_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:24:13.437624+00:00
-- url     : https://prove2.me/submissions/453306ab-7323-4fe6-8a96-ef854bd6e385

import Mathlib
import Definitions.Def_Tropical_TropicalLinearSpaceElimination
open TropicalElimination in
theorem solution {E : Type*} [Nontrivial E] [Fintype E] [Nonempty E] [Fintype E] [DecidableEq E]
    [Nontrivial E] [Fintype E] [Nonempty E] (c : E → TT) (hc : ∀ i, c i ≠ ⊤) {x : E → TT}
    (hx : x ∈ tropVanishing c) (hx0 : x ≠ tropZero E) :
    ∃ i j, i ≠ j ∧ x i ≠ ⊤ ∧ x j ≠ ⊤ := by
  -- some coordinate is finite
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ ⊤ := by
    by_contra h
    push_neg at h
    exact hx0 (funext fun k => h k)
  -- its vanishing witness `j ≠ i` is bounded by a finite value, so is finite too
  obtain ⟨j, hji, hj⟩ := hx i
  have h1 : c i + x i ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hc i, hi⟩
  have h2 : c j + x j ≠ ⊤ := ne_top_of_le_ne_top h1 hj
  exact ⟨i, j, fun h => hji h.symm, hi, (WithTop.add_ne_top.mp h2).2⟩
