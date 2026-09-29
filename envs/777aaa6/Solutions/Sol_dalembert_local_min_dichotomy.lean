-- Prove2me | solution 1 for dalembert_local_min_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-22T14:09:34.843479+00:00
-- url     : https://prove2.me/submissions/a65f21e9-9cba-4fe6-bc8a-159a21dad252

import Theorems.Thm_dalembert_local_min_dichotomy
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Solution — `dalembert_local_min_dichotomy` (Child 2)

Direct proof: apply Mathlib's
`Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm` to the entire function
`z ↦ f.eval z`. Its differentiability everywhere is `Polynomial.differentiableAt`,
and `norm ∘ (f.eval ·)` is definitionally `fun z => ‖f.eval z‖`, so the local-min
hypothesis transfers directly.

`theorem solution` matches the target type of
`Thm_dalembert_local_min_dichotomy`; submit with `proof_type=prove`.
-/

open Polynomial Filter Topology

theorem solution {f : ℂ[X]} {c : ℂ}
    (hc : IsLocalMin (fun z => ‖f.eval z‖) c) :
    (∀ᶠ z in 𝓝 c, f.eval z = f.eval c) ∨ f.eval c = 0 :=
  Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm
    (Eventually.of_forall fun _ => f.differentiableAt) hc
