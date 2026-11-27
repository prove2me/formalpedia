-- Prove2me | Theorems.Thm_WorldLine_causal_type_invariant
-- name    : WorldLine.causal_type_invariant
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T02:10:18.266435+00:00
-- url     : https://prove2.me/theorems/6e92cc62-d11d-5667-862d-5ae74c34a725
-- title:
--   The causal classification is frame-independent (light cones preserved)
-- statement:
--   **Causal classification is frame-independent — entry rung.**
--
--   Let `A` be a Lorentz transformation ($A^{T}\eta A = \eta$) and let `u` be a separation vector.
--
--   **Conclusion:** a two-fold implication — if `u` is timelike ($\eta(u,u) < 0$) then the transformed separation `A.mulVec u` is timelike, and if `u` is null ($\eta(u,u) = 0$) then `A.mulVec u` is null.
--
--   In words: every observer related by a Lorentz transformation classifies separations identically — the timelike class (realizable by massive particles, "with a speed less than the speed of light") and the null class (realizable by light, "having at each point the speed of light") are preserved. This is the source's "the light cones are the same for all observers at a given spacetime event": the cone structure that divides spacetime into future, past, light cone and elsewhere is observer-independent.
--
--   **Formalization note.** Computation: $\eta(Au, Au) = (Au)^{T}\eta(Au) = u^{T}(A^{T}\eta A)u = \eta(u,u)$, then strict-inequality and equality preservation. Spacelike preservation follows by the same computation but is not asserted separately (it is the contrapositive-complement of the two stated cases).
-- source:
--   Wikipedia, World line, https://en.wikipedia.org/wiki/World_line (source of the quoted statements, reproduced verbatim in the definition file) (curve types: 'light-like curves, having at each point the speed of light'; 'time-like curves, with a speed less than the speed of light'; 'the light cones are the same for all observers at a given spacetime event'); H. Minkowski, Raum und Zeit (1908)

import Mathlib
import Definitions.Def_WorldLine

namespace WorldLine

open Matrix

/-- Milestone: the causal classification of curves is frame-independent —
"the light cones are the same for all observers at a given spacetime event".
A Lorentz transformation carries timelike tangents to timelike tangents (the
class of time-like curves, "with a speed less than the speed of light") and
null tangents to null tangents (the class of light-like curves, "having at
each point the speed of light"). -/
theorem causal_type_invariant (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : IsLorentz A)
    (u : Sp) : (IsTimelike u → IsTimelike (A.mulVec u)) ∧ (IsNull u → IsNull (A.mulVec u)) := by
  sorry

end WorldLine
