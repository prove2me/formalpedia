-- Prove2me | solution 1 for QuasiSymmetricComposition.dimH_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T14:54:16.758286+00:00
-- url     : https://prove2.me/submissions/4ee1937a-b91c-471d-9e64-ca2b6af89d42

import Mathlib
import Definitions.Def_Geometry_NumberTheory_QuasiSymmetricComposition

open MeasureTheory Set Function QuasiSymmetricComposition NNReal ENNReal in
theorem solution {X Y : Type*} [EMetricSpace X] [EMetricSpace Y] {K K' : ℝ≥0} {f : X → Y}
    {s : Set X} [Nonempty X] (hL : LipschitzOnWith K f s)
    (hA : AntilipschitzOnWith K' f s) : dimH (f '' s) = dimH s := by
  refine le_antisymm hL.dimH_image_le ?_
  -- antilipschitz on `s` makes `f` injective there
  have hinj : Set.InjOn f s := by
    intro x hx y hy hxy
    have h := hA hx hy
    rw [hxy, edist_self, mul_zero] at h
    exact edist_le_zero.1 h
  -- the inverse on the image is `K'`-Lipschitz
  have hg : LipschitzOnWith K' (Function.invFunOn f s) (f '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hinj.leftInvOn_invFunOn hx, hinj.leftInvOn_invFunOn hy]
    exact hA hx hy
  have hs : s ⊆ Function.invFunOn f s '' (f '' s) :=
    fun x hx => ⟨f x, ⟨x, hx, rfl⟩, hinj.leftInvOn_invFunOn hx⟩
  calc dimH s ≤ dimH (Function.invFunOn f s '' (f '' s)) := dimH_mono hs
    _ ≤ dimH (f '' s) := hg.dimH_image_le
