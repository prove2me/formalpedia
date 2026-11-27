-- Prove2me | Theorems.Thm_WorldLine_inertial_proper_time
-- name    : WorldLine.inertial_proper_time
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T02:11:06.84026+00:00
-- url     : https://prove2.me/theorems/1cf14866-a14e-4f62-9b3a-ace546594ad2
-- title:
--   Proper time of a straight (inertial) worldline
-- statement:
--   **Proper time of a straight (inertial) worldline.**
--
--   Let `a v : Sp` with `v` timelike ($\eta(v,v) < 0$, so $\sqrt{-\eta(v,v)}$ is real), and let the worldline be the affine curve $\gamma(t) = a + t\,v$ — "a tilted line represents a particle with a constant coordinate speed".
--
--   **Conclusion:** between parameter values $t_1, t_2$ the proper time is
--
--   $$\Delta\tau \;=\; \sqrt{-\eta(v, v)}\,\cdot\,(t_2 - t_1).$$
--
--   In words: the length of the straight worldline segment — its proper time, per Harvey "The length of M is called the proper time of the particle" — is the Minkowski norm of the velocity times the elapsed parameter. For the coordinate-time parametrization $v_0 = 1$ (one time-unit per parameter-unit) one has $-\eta(v,v) = 1 - s^2$ with $s$ the spatial speed, and this is exactly the time-dilation factor $\sqrt{1 - s^2}$ of the familiar $\Delta t' = \gamma\,\Delta t$: the moving clock records less time than the coordinate clock, in exact proportion.
--
--   **Formalization note.** The derivative of an affine map is constant (`deriv γ t = v` for all `t`, via Mathlib's `deriv_const_add`), so the proper-time integrand $\sqrt{-\eta(v,v)}$ is constant and the assertion is the integral of a constant over $t_1 \,.\,.\, t_2$. No hypothesis on the parametrization beyond timelikeness of `v`: the statement is parametrization-covariant (rescaling $t$ rescales both sides consistently).
-- source:
--   Wikipedia, World line, https://en.wikipedia.org/wiki/World_line (source of the quoted statements, reproduced verbatim in the definition file) (Harvey quote: 'The length of M is called the proper time of the particle'; 'A tilted line represents a particle with a constant coordinate speed')

import Mathlib
import Definitions.Def_WorldLine

namespace WorldLine

open Matrix

/-- Milestone: the proper time of a straight worldline.  For an inertial
worldline `γ t = a + t v` with timelike velocity `v` — "a line at constant
speed ... a particle with a constant coordinate speed" — the length of the
worldline segment between parameters `t₁` and `t₂` (its proper time, per
Harvey: "The length of M is called the proper time of the particle") is

`Δτ = √(-η(v, v)) · (t₂ - t₁)`,

the elapsed time on a clock carried by the particle, in natural units `c = 1`.
For the coordinate-time parametrization `v 0 = 1` this is the time-dilation
factor `√(1 - s²)` of the source's `Δt' = γ Δt`. -/
theorem inertial_proper_time (a v : Sp) (hv : IsTimelike v) (t₁ t₂ : ℝ) :
    properTime (fun t => a + t • v) t₁ t₂ = Real.sqrt (-(mink v v)) * (t₂ - t₁) := by
  sorry

end WorldLine
