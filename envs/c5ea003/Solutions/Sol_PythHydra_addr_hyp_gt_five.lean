-- Prove2me | solution 1 for PythHydra.addr_hyp_gt_five
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:29:25.160315+00:00
-- url     : https://prove2.me/submissions/df1725a1-3b52-4aaa-b56f-f723135a248c

import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent
open PythHydra in
theorem solution (s : BStep) (w : List BStep) : 5 < (addr (s :: w)).2.2 := by
  have hppt : ∀ w : List BStep, IsPPT (addr w).1 (addr w).2.1 (addr w).2.2 := by
    intro w
    induction w with
    | nil => exact root_isPPT
    | cons s w ih =>
      cases s
      · exact bergA_isPPT ih
      · exact bergB_isPPT ih
      · exact bergC_isPPT ih
  have hgrowc : ∀ (s : BStep) (t : ℤ × ℤ × ℤ), IsPPT t.1 t.2.1 t.2.2 →
      t.2.2 < (applyStep s t).2.2 := by
    rintro s ⟨a, b, c⟩ h
    obtain ⟨hac, hbc⟩ := h.legs_lt
    have := h.ha
    have := h.hb
    cases s <;> simp only [applyStep, bergA_snd_snd, bergB_snd_snd, bergC_snd_snd] <;> linarith
  have hc5 : ∀ w : List BStep, 5 ≤ (addr w).2.2 := by
    intro w
    induction w with
    | nil => simp [addr]
    | cons s w ih =>
      have := hgrowc s (addr w) (hppt w)
      simp only [addr]
      linarith
  have hgt5 : ∀ (s : BStep) (w : List BStep), 5 < (addr (s :: w)).2.2 := by
    intro s w
    have := hgrowc s (addr w) (hppt w)
    have := hc5 w
    simp only [addr]
    linarith
  exact hgt5 s w
