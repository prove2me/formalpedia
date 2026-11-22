-- Prove2me | Theorems.Thm_GL_mem_range_map_iff
-- name    : GL.mem_range_map_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:41.732267+00:00
-- url     : https://prove2.me/theorems/84e10b74-7e76-421f-a2ef-4a06120e83fb
-- title:
--   GL: mem range map iff
-- statement:
--   The GL construction uses the mem range map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L82-L96
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L82-L96

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem GL.mem_range_map_iff {f : R →+* S} (hf : Function.Injective f)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : GL ι S) :
    g ∈ Set.range (Matrix.GeneralLinearGroup.map f) ↔
      (∀ (i j : ι), g i j ∈ Set.range f) ∧
        ↑g.det⁻¹ ∈ Set.range f := by sorry
