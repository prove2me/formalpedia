-- Prove2me | solution 1 for MovingSofa.ForMathlib.hasDerivAt_comp_add_const_iff
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-29T22:14:38.528079+00:00
-- url     : https://prove2.me/submissions/ee5e558e-eff0-4d6f-bde1-a386ebd0b4bb

import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit false

theorem solution {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {f' : F} (x a : 𝕜) :
    HasDerivAt (fun u ↦ f (u + a)) f' x ↔ HasDerivAt f f' (x + a) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_add_const x a⟩
  have h' : HasDerivAt (fun u ↦ f (u + a)) f' (x + a + -a) := by simpa using h
  simpa using h'.comp_add_const (x + a) (-a)
