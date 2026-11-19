-- Prove2me | solution 1 for A166944Research.a166944_quiet_window_of_caps
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-19T00:22:26.514647+00:00
-- url     : https://prove2.me/submissions/05faf07d-275b-45f8-afbb-983a778a787c

import Definitions.Def_a166944_window_core

open A166944Research

/-- The quiet-window condition, division-free: the cap arithmetic alone gives it,
for any `q` with `q * q <= Cf + 1`. This is `WindowCore.window_condition` applied
directly; no square root and no Mathlib import are involved. -/
theorem solution {M sf Cf q : Nat} (hM : 968 ≤ M)
    (hindex : 4 * sf ≤ 7 * M - 1) (hlo : 2 * M - 2 ≤ Cf)
    (hhorizon : Cf ≤ 3 * M + 4) (hq : q * q ≤ Cf + 1) :
    2 * q < Cf - sf :=
  window_condition M sf Cf q hM hindex hlo hhorizon hq
