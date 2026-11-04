-- Prove2me | solution 1 for MovingSofa.ForMathlib.contDiff_one_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:57:23.309825+00:00
-- url     : https://prove2.me/submissions/6f12db1b-6696-4f11-84d6-837a69dd17d9

import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open Set

theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') :
    ContDiff ℝ 1 f :=
  contDiff_one_iff_deriv.2 ⟨fun t => (hf t).differentiableAt, deriv_eq hf ▸ hf'⟩
