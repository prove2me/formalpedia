-- Prove2me | Theorems.Thm_WorldLine_proper_time_lorentz_invariant
-- name    : WorldLine.proper_time_lorentz_invariant
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T02:11:34.895128+00:00
-- url     : https://prove2.me/theorems/8ac809c8-8001-42d6-a34d-fd2bdcc34429
-- title:
--   Proper time is frame-independent
-- statement:
--   **Proper time is frame-independent.**
--
--   Let `A` be a Lorentz transformation ($A^{T}\eta A = \eta$) and let $\gamma : \mathbb{R} \to Sp$ be a continuously differentiable worldline (`ContDiff ℝ 1 γ`).
--
--   **Conclusion:** the proper time of the transformed worldline equals the proper time of the original:
--
--   $$\mathrm{properTime}(t \mapsto A\cdot\gamma(t),\ t_1, t_2) \;=\; \mathrm{properTime}(\gamma,\ t_1, t_2).$$
--
--   In words: all inertial observers — related by Lorentz transformations — agree on the time elapsed on the clock carried by the worldline. This is the arclength form of the invariance of the interval: although the coordinates of every event change under the passage to another frame, the proper time - the timelike arclength of the interval - is the same for all observers, whatever their relative velocity.
--
--   **Formalization note.** Chain rule + invariance: the derivative of $t \mapsto A \cdot \gamma(t)$ is $A\cdot\gamma'(t)$ (the action of the matrix is linear in the vector; Mathlib's derivative rules for continuous linear maps), so the transformed integrand is $\sqrt{-\eta(A\gamma', A\gamma')} = \sqrt{-\gamma'^{T}(A^{T}\eta A)\gamma'} = \sqrt{-\eta(\gamma', \gamma')}$ — the integrands agree pointwise and so do the integrals. The `ContDiff ℝ 1 γ` hypothesis guarantees `deriv γ` exists everywhere, as the proper-time integrand requires; no timelikeness hypothesis is needed for the equality (it holds formally for any $C^1$ curve).
-- source:
--   Wikipedia, World line, https://en.wikipedia.org/wiki/World_line (source of the quoted statements, reproduced verbatim in the definition file) (special relativity: 'The structure of spacetime is determined by a bilinear form eta'; inertial coordinate systems 'in which the speed of light is a constant'); H. Minkowski, Raum und Zeit (1908)

import Mathlib
import Definitions.Def_WorldLine

namespace WorldLine

open Matrix

/-- Milestone: proper time is frame-independent.  Applying a Lorentz
transformation — the change between inertial coordinate systems, in which
"the speed of light is a constant" — to every point of a continuously
differentiable worldline leaves its proper time unchanged:

`properTime (A ∘ γ) t₁ t₂ = properTime γ t₁ t₂`.

This is the invariance of the "interval" under the passage between observers:
all observers agree on the time elapsed on the clock carried by the worldline. -/
theorem proper_time_lorentz_invariant (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : IsLorentz A)
    (γ : ℝ → Sp) (hγ : ContDiff ℝ 1 γ) (t₁ t₂ : ℝ) :
    properTime (fun t => A.mulVec (γ t)) t₁ t₂ = properTime γ t₁ t₂ := by
  sorry

end WorldLine
