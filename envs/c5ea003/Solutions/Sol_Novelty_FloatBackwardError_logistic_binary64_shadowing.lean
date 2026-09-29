-- Prove2me | solution 1 for Novelty.FloatBackwardError.logistic_binary64_shadowing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:16:38.320888+00:00
-- url     : https://prove2.me/submissions/29466ad2-0dc7-4873-8482-b6da41afa8f2

-- Sol generated from Novelty/FloatPseudoOrbitShadowing.lean
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing
import Theorems.Thm_Novelty_FloatBackwardError_binary64_defect_bound
import Theorems.Thm_Novelty_FloatBackwardError_finite_shadowing
import Theorems.Thm_Novelty_FloatBackwardError_flOrbit_isPseudoOrbit
import Theorems.Thm_Novelty_FloatBackwardError_gamma_nonneg
import Theorems.Thm_Novelty_FloatBackwardError_hornerAbs_nonneg
import Theorems.Thm_Novelty_FloatBackwardError_hornerR_logisticCoeffs
import Theorems.Thm_Novelty_FloatBackwardError_trueOrbit_logistic_mem

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







/-- On the unit interval the logistic map is `4`-Lipschitz, and this is the
expansion rate responsible for the exponential factor in the shadowing bound. -/
lemma logistic_lipschitz : ∀ a ∈ Set.Icc (0:ℝ) 1, ∀ b ∈ Set.Icc (0:ℝ) 1,
    |logistic a - logistic b| ≤ 4 * |a - b| := by
  rintro a ⟨ha0, ha1⟩ b ⟨hb0, hb1⟩
  have hfac : logistic a - logistic b = (a - b) * (4 * (1 - a - b)) := by
    simp [logistic]; ring
  rw [hfac, abs_mul]
  have h1 : |4 * (1 - a - b)| ≤ 4 := by
    rw [abs_le]
    constructor <;> nlinarith
  have h2 : (0:ℝ) ≤ |a - b| := abs_nonneg _
  nlinarith




open Novelty.FloatBackwardError in
theorem solution(M : RoundingModel) (hu : M.u ≤ (2:ℝ) ^ (-53 : ℤ))
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) (N : ℕ)
    (hstay : ∀ n ≤ N, flOrbit M logisticCoeffs x₀ n ∈ Set.Icc (0:ℝ) 1) :
    ∀ n ≤ N, |flOrbit M logisticCoeffs x₀ n - trueOrbit logistic x₀ n|
      ≤ (2:ℝ) ^ (-46 : ℤ) * (((4:ℝ) ^ n - 1) / 3) := by
  set x := flOrbit M logisticCoeffs x₀ with hxdef
  have hx0 : x 0 = x₀ := rfl
  -- Semantics layer: the execution is a certified pseudo-orbit of the exact map.
  have hmag : ∀ n ≤ N, |x n| ≤ 1 := by
    intro n hn
    obtain ⟨h0, h1⟩ := hstay n hn
    rw [abs_of_nonneg h0]; exact h1
  have hpo0 := flOrbit_isPseudoOrbit M logisticCoeffs x₀ 1 N hmag
  have hfun : (fun z => hornerR logisticCoeffs z) = logistic := by
    funext z; exact hornerR_logisticCoeffs z
  rw [hfun] at hpo0
  set δ := gamma M.u (2 * logisticCoeffs.length) * hornerAbs logisticCoeffs 1 with hδdef
  have hδnonneg : 0 ≤ δ :=
    mul_nonneg (gamma_nonneg M.u_nonneg _) (hornerAbs_nonneg _ _)
  have hδ : δ ≤ (2:ℝ) ^ (-46 : ℤ) := binary64_defect_bound M.u_nonneg hu
  -- Dynamics layer: finite-time shadowing with Lipschitz constant 4.
  have hy : ∀ n ≤ N, trueOrbit logistic (x 0) n ∈ Set.Icc (0:ℝ) 1 := by
    intro n _
    rw [hx0]
    exact trueOrbit_logistic_mem hx₀ n
  have hshadow := finite_shadowing (L := 4) (by norm_num) logistic_lipschitz
    (fun n hn => hstay n hn) hy hpo0
  intro n hn
  refine (hshadow n hn).trans ?_
  have hsum : (∑ k ∈ Finset.range n, (4:ℝ) ^ k) = ((4:ℝ) ^ n - 1) / 3 := by
    rw [geom_sum_eq (by norm_num) n]
    norm_num
  have hsum_nonneg : (0:ℝ) ≤ ((4:ℝ) ^ n - 1) / 3 := by
    have : (1:ℝ) ≤ (4:ℝ) ^ n := one_le_pow₀ (by norm_num)
    linarith
  rw [hx0] at *
  rw [hsum]
  exact mul_le_mul_of_nonneg_right hδ hsum_nonneg
