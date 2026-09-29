-- Prove2me | solution 1 for Novelty.FloatBackwardError.logistic_aposteriori_shadowing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:16:37.816733+00:00
-- url     : https://prove2.me/submissions/2a21f07e-32a2-4d96-b2ef-55ef4dbfe623

-- Sol generated from Novelty/FloatShadowingSharpness.lean
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing
import Definitions.Def_Novelty_FloatShadowingSharpness
import Theorems.Thm_Novelty_FloatBackwardError_binary64_defect_bound
import Theorems.Thm_Novelty_FloatBackwardError_flOrbit_isPseudoOrbit
import Theorems.Thm_Novelty_FloatBackwardError_hornerR_logisticCoeffs
import Theorems.Thm_Novelty_FloatBackwardError_logistic_local_lipschitz
import Theorems.Thm_Novelty_FloatBackwardError_trueOrbit_logistic_mem
import Theorems.Thm_Novelty_FloatBackwardError_variable_shadowing

/-!
# Nonautonomous shadowing bounds and their sharpness

Third cycle of the programme.  Two questions left open by the previous cycles
are settled here.

1. *Is the uniform Lipschitz constant necessary?*  No: `variable_shadowing`
   replaces `L` by the observed, step-dependent local expansion factors `L n`,
   producing the a-posteriori error recursion `E 0 = 0`,
   `E (n+1) = δ + L n · E n`.  Specialising to a constant sequence recovers the
   geometric bound (`errBound_const`), so the nonautonomous statement is a
   strict refinement.

2. *Is the exponential growth of the forward bound an artifact of the proof?*
   No: `finite_shadowing_sharp` exhibits, for every `L ≥ 0` and `δ ≥ 0`, an
   `L`-Lipschitz map and a `δ`-pseudo-orbit for which the distance to the true
   orbit **equals** `δ (1 + L + ⋯ + L^{n-1})` at every step.  Hence the forward
   shadowing theorem of the first cycle cannot be improved, and the improvement
   obtained in the second cycle (`expanding_backward_shadowing`) genuinely
   requires moving the initial condition.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the geometric factor in forward shadowing is exactly
attained by the linear map `z ↦ L z` driven by a constant defect `δ`, so no
proof technique can remove it while keeping the initial point fixed.
Experiment (Experimenter): the witness is the affine recursion
`x_{n+1} = L xₙ + δ` started at `0`, whose true orbit is identically `0`; the
distance is the geometric sum, verified by induction (`sharpWitness_eq`).
Analysis (Analyst): the three cycles now separate cleanly:
semantics (`O(u)` defect) → forward dynamics (`O(u · Lⁿ)`, sharp) →
backward dynamics under expansivity (`O(u)`, uniform in n).
Critique (Critic): the sharpness witness is an honest pseudo-orbit — its defect
is exactly `δ` at every step, not merely bounded by `δ` — and the map is exactly
`L`-Lipschitz, so no slack is hidden in the hypotheses.
-- !-- End Lab Notes -- !--
-/

open Novelty.FloatBackwardError

open scoped BigOperators





/-! ### Sharpness of the forward shadowing bound -/





/-! ### The a-posteriori bound for a binary64 logistic execution -/

lemma errBound_mono_delta {δ₁ δ₂ : ℝ} {L : ℕ → ℝ} (hL : ∀ n, 0 ≤ L n)
    (h : δ₁ ≤ δ₂) : ∀ n, errBound δ₁ L n ≤ errBound δ₂ L n := by
  intro n
  induction n with
  | zero => simp [errBound]
  | succ n ih =>
      have := mul_le_mul_of_nonneg_left ih (hL n)
      simp only [errBound]
      linarith




open Novelty.FloatBackwardError in
theorem solution(M : RoundingModel)
    (hu : M.u ≤ (2:ℝ) ^ (-53 : ℤ)) (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) (N : ℕ)
    (hstay : ∀ n ≤ N, flOrbit M logisticCoeffs x₀ n ∈ Set.Icc (0:ℝ) 1) :
    ∀ n ≤ N, |flOrbit M logisticCoeffs x₀ n - trueOrbit logistic x₀ n|
      ≤ errBound ((2:ℝ) ^ (-46 : ℤ))
          (fun k => 4 * max (flOrbit M logisticCoeffs x₀ k)
            (1 - flOrbit M logisticCoeffs x₀ k)) n := by
  set x := flOrbit M logisticCoeffs x₀ with hxdef
  set L : ℕ → ℝ := fun k => 4 * max (x k) (1 - x k) with hLdef
  have hx0 : x 0 = x₀ := rfl
  have hL : ∀ n, 0 ≤ L n := by
    intro n
    have h1 : x n ≤ max (x n) (1 - x n) := le_max_left _ _
    have h2 : 1 - x n ≤ max (x n) (1 - x n) := le_max_right _ _
    simp only [hLdef]
    linarith
  have hmag : ∀ n ≤ N, |x n| ≤ 1 := by
    intro n hn
    obtain ⟨h0, h1⟩ := hstay n hn
    rw [abs_of_nonneg h0]; exact h1
  have hpo := flOrbit_isPseudoOrbit M logisticCoeffs x₀ 1 N hmag
  have hfun : (fun z => hornerR logisticCoeffs z) = logistic := by
    funext z; exact hornerR_logisticCoeffs z
  rw [hfun] at hpo
  have hy : ∀ n ≤ N, trueOrbit logistic (x 0) n ∈ Set.Icc (0:ℝ) 1 := by
    intro n _
    rw [hx0]
    exact trueOrbit_logistic_mem hx₀ n
  have hLip : ∀ n < N, ∀ b ∈ Set.Icc (0:ℝ) 1,
      |logistic (x n) - logistic b| ≤ L n * |x n - b| := by
    intro n hn b hb
    exact logistic_local_lipschitz (hstay n (le_of_lt hn)) b hb
  have hmain := variable_shadowing hL hLip hy hpo
  intro n hn
  refine (hmain n hn).trans ?_
  exact errBound_mono_delta hL (binary64_defect_bound M.u_nonneg hu) n
