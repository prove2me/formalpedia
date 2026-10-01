-- Prove2me | solution 1 for MovingSofa.ForMathlib.abs_sInf_image_sub_sInf_image_le
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:16:05.113124+00:00
-- url     : https://prove2.me/submissions/8fe9e56e-3207-455f-9780-4022c4522d9f

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

theorem solution {ι : Type*} {s : Set ι}
    (hs : s.Nonempty) (f g : ι → ℝ) (hf : BddBelow (f '' s)) (hg : BddBelow (g '' s))
    {C : ℝ} (h : ∀ x ∈ s, |f x - g x| ≤ C) :
    |sInf (f '' s) - sInf (g '' s)| ≤ C := by
  have hfg : sInf (f '' s) - C ≤ sInf (g '' s) := by
    apply le_csInf (hs.image g)
    rintro _ ⟨x, hx, rfl⟩
    have hfx : sInf (f '' s) ≤ f x := csInf_le hf ⟨x, hx, rfl⟩
    have hpoint := (abs_le.mp (h x hx)).2
    linarith
  have hgf : sInf (g '' s) - C ≤ sInf (f '' s) := by
    apply le_csInf (hs.image f)
    rintro _ ⟨x, hx, rfl⟩
    have hgx : sInf (g '' s) ≤ g x := csInf_le hg ⟨x, hx, rfl⟩
    have hpoint := (abs_le.mp (h x hx)).1
    linarith
  rw [abs_le]
  constructor <;> linarith
