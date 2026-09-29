-- Prove2me | solution 2 for PythHydra.exists_addr
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T18:54:32.772712+00:00
-- url     : https://prove2.me/submissions/6722534d-44db-4d55-8db5-34a485e596ae

import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent
open PythHydra in
theorem solution {a b c : ℤ} (h : IsPPT a b c) : ∃ w : List BStep, addr w = (a, b, c) := by
  have hreach_addr : ∀ t, Reach t → ∃ w : List BStep, addr w = t := by
    intro t ht
    induction ht with
    | root => exact ⟨[], rfl⟩
    | stepA _ ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨BStep.A :: w, by simp only [addr, applyStep, hw]⟩
    | stepB _ ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨BStep.B :: w, by simp only [addr, applyStep, hw]⟩
    | stepC _ ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨BStep.C :: w, by simp only [addr, applyStep, hw]⟩
  exact hreach_addr _ ((reach_iff_isPPT _ _ _).mpr h)
