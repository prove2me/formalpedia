-- Prove2me | solution 1 for polynomial_eval_norm_tendsto_cobounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-22T14:36:18.647757+00:00
-- url     : https://prove2.me/submissions/27af1c24-6495-43eb-96c3-a4efa86ca228

import Theorems.Thm_polynomial_eval_norm_tendsto_cobounded
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Solution — `polynomial_eval_norm_tendsto_cobounded` (Liouville Child 1)

Direct proof via `Polynomial.tendsto_norm_atTop` with `z = id` and the
`cobounded` filter (along which `‖·‖ → ∞`, witnessed by
`tendsto_norm_cobounded_atTop`).
-/

open Polynomial Filter

theorem solution {f : ℂ[X]} (hf : 0 < degree f) :
    Tendsto (fun z : ℂ => ‖f.eval z‖) (Bornology.cobounded ℂ) atTop :=
  f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop
