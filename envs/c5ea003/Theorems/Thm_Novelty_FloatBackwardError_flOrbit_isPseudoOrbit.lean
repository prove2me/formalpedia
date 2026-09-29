-- Prove2me | Theorems.Thm_Novelty_FloatBackwardError_flOrbit_isPseudoOrbit
-- name    : Novelty.FloatBackwardError.flOrbit_isPseudoOrbit
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:13:48.851501+00:00
-- url     : https://prove2.me/theorems/0e8277c3-ad49-44c5-80e0-6a2b8d2d3bc2
-- title:
--   Semantic translation theorem.
-- statement:
--   **Semantic translation theorem.**  A finite floating-point execution of the
--   polynomial iteration `x ↦ p(x)` that is observed to stay within magnitude `B` is
--   an exact real `δ`-pseudo-orbit of the exact map, with the *compositional* local
--   defect `δ = γ_{2n}(u) · Σ|aᵢ| Bⁱ`.
--
--   ```lean
--   theorem Novelty.FloatBackwardError.flOrbit_isPseudoOrbit(M : RoundingModel) (as : List ℝ) (x₀ B : ℝ)
--       (N : ℕ) (hB : ∀ n ≤ N, |flOrbit M as x₀ n| ≤ B) :
--       IsPseudoOrbit (fun z => hornerR as z)
--         (gamma M.u (2 * as.length) * hornerAbs as B) (flOrbit M as x₀) N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FloatPseudoOrbitShadowing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FloatPseudoOrbitShadowing.lean#L87

-- Thm stub generated from Novelty/FloatPseudoOrbitShadowing.lean
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing

/-!
# From floating-point executions to certified pseudo-orbits, and shadowing

This file completes the programme begun in `Novelty.FloatBackwardErrorHorner`:

1. **Semantics layer.**  A finite floating-point execution of a polynomial
   iteration (Horner evaluation at each step, in an execution free of overflow,
   underflow and exceptional values) *is* an exact real pseudo-orbit of the exact
   polynomial map, with a local defect bounded by
   `γ_{2n}(u) · Σ |aᵢ| Bⁱ`, a compositional expression in the unit roundoff `u`
   and the intermediate magnitude bound `B` (`flOrbit_isPseudoOrbit`).
   Moreover each step is *exactly* a step of a perturbed polynomial map whose
   coefficients are relatively within `γ_{2n}(u)` of the nominal ones
   (`flOrbit_nonautonomous_exact`): backward-error semantics.

2. **Dynamics layer.**  An abstract finite-time shadowing theorem
   (`finite_shadowing`) consumes exactly such a defect certificate and produces a
   true orbit tracking the execution; `contraction_shadowing` gives a
   time-uniform bound when the map is a contraction on the region visited.

3. **Instantiation.**  For the logistic map `f x = 4x(1-x)` implemented in IEEE
   binary64 (`u = 2⁻⁵³`) the two layers compose into a fully explicit
   a-posteriori error bound (`logistic_binary64_shadowing`): any execution
   observed to stay in `[0,1]` is shadowed, for `n ≤ N` steps, by the *exact*
   real logistic orbit started at the same point, to within `2⁻⁴⁷ (4ⁿ - 1)/3`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the "chaos destroys floating-point simulation"
folklore conflates two separable statements: a *semantic* one (each step is
exact for a nearby polynomial) and a *dynamical* one (nearby pseudo-orbits are
shadowed).  Only the second involves the Lyapunov exponent.
Experiment (Experimenter): formalizing the split.  The semantic layer is
unconditional (no hypothesis on the dynamics at all) once the execution is
observed to avoid overflow; the dynamical layer needs only a Lipschitz constant
on the visited region, which is an a-posteriori computable quantity.
Analysis (Analyst): the composed logistic bound `2⁻⁴⁷ (4ⁿ-1)/3` becomes vacuous
around n ≈ 23 steps, matching the standard heuristic "one decimal digit lost per
0.6 steps at λ = log 4"; the exponential factor comes *only* from the dynamics
layer, confirming the separation hypothesis.
Critique (Critic): the Lipschitz constant `4` used for the logistic map is the
global one on `[0,1]`; using the observed local constant `|4 - 8xₙ|` would give a
sharper (nonautonomous) product bound.  This is recorded as a future direction.
The hypothesis "the execution stays in [0,1]" is not vacuous: it is exactly the
runtime check that no overflow/exceptional value occurred, and it is satisfiable
(the exact orbit of any `x₀ ∈ [0,1]` stays in `[0,1]`, `logistic_maps_unitInterval`).
-- !-- End Lab Notes -- !--
-/

open Novelty.FloatBackwardError

open scoped BigOperators

/-! ### Pseudo-orbits -/




/-! ### The magnitude functional is monotone -/


/-! ### Semantics layer: a floating-point execution is a certified pseudo-orbit -/

theorem Novelty.FloatBackwardError.flOrbit_isPseudoOrbit(M : RoundingModel) (as : List ℝ) (x₀ B : ℝ)
    (N : ℕ) (hB : ∀ n ≤ N, |flOrbit M as x₀ n| ≤ B) :
    IsPseudoOrbit (fun z => hornerR as z)
      (gamma M.u (2 * as.length) * hornerAbs as B) (flOrbit M as x₀) N := by sorry
