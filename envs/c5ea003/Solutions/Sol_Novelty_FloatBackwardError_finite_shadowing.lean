-- Prove2me | solution 1 for Novelty.FloatBackwardError.finite_shadowing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:13:06.422717+00:00
-- url     : https://prove2.me/submissions/64df2525-51f4-4df3-aba3-c2adbbc0527f

-- Sol generated from Novelty/FloatPseudoOrbitShadowing.lean
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



/-! ### Dynamics layer: finite-time shadowing -/



/-! ### Instantiation: the logistic map at parameter 4 in IEEE binary64 -/











open Novelty.FloatBackwardError in
theorem solution{f : ℝ → ℝ} {L δ : ℝ} {S : Set ℝ} (hL : 0 ≤ L)
    (hLip : ∀ a ∈ S, ∀ b ∈ S, |f a - f b| ≤ L * |a - b|)
    {x : ℕ → ℝ} {N : ℕ}
    (hx : ∀ n ≤ N, x n ∈ S)
    (hy : ∀ n ≤ N, trueOrbit f (x 0) n ∈ S)
    (hpo : IsPseudoOrbit f δ x N) :
    ∀ n ≤ N, |x n - trueOrbit f (x 0) n| ≤ δ * ∑ k ∈ Finset.range n, L ^ k := by
  intro n
  induction n with
  | zero => intro _; simp [trueOrbit]
  | succ n ih =>
      intro hn
      have hnN : n ≤ N := Nat.le_of_succ_le hn
      have hn' : n < N := hn
      have hprev := ih hnN
      have hstep : |x (n + 1) - f (x n)| ≤ δ := hpo n hn'
      have hlip : |f (x n) - f (trueOrbit f (x 0) n)| ≤ L * |x n - trueOrbit f (x 0) n| :=
        hLip _ (hx n hnN) _ (hy n hnN)
      have htri : |x (n + 1) - trueOrbit f (x 0) (n + 1)|
          ≤ |x (n + 1) - f (x n)| + |f (x n) - f (trueOrbit f (x 0) n)| := by
        have : x (n + 1) - trueOrbit f (x 0) (n + 1)
            = (x (n + 1) - f (x n)) + (f (x n) - f (trueOrbit f (x 0) n)) := by
          simp [trueOrbit]
        rw [this]
        exact abs_add_le _ _
      have hgeom : (∑ k ∈ Finset.range (n + 1), L ^ k)
          = L * (∑ k ∈ Finset.range n, L ^ k) + 1 := geom_sum_succ
      calc |x (n + 1) - trueOrbit f (x 0) (n + 1)|
          ≤ δ + L * |x n - trueOrbit f (x 0) n| := by linarith
        _ ≤ δ + L * (δ * ∑ k ∈ Finset.range n, L ^ k) := by
            linarith [mul_le_mul_of_nonneg_left hprev hL]
        _ = δ * (L * (∑ k ∈ Finset.range n, L ^ k) + 1) := by ring
        _ = δ * ∑ k ∈ Finset.range (n + 1), L ^ k := by rw [hgeom]
