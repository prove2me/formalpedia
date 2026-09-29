-- Prove2me | solution 1 for Novelty.FloatBackwardError.cubic_fl_shadowed_uniformly
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:13:05.793519+00:00
-- url     : https://prove2.me/submissions/ce8dd6e7-bb9c-4a4b-9705-d80905ff6d0a

-- Sol generated from Novelty/FloatExpandingShadowing.lean
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatExpandingShadowing
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing
import Theorems.Thm_Novelty_FloatBackwardError_expanding_backward_shadowing
import Theorems.Thm_Novelty_FloatBackwardError_flOrbit_isPseudoOrbit
import Theorems.Thm_Novelty_FloatBackwardError_gamma_nonneg
import Theorems.Thm_Novelty_FloatBackwardError_hornerAbs_nonneg

/-!
# Uniform-in-time shadowing of floating-point executions of expanding polynomials

The finite-time shadowing bound `δ (Lⁿ - 1)/(L - 1)` of
`Novelty.FloatPseudoOrbitShadowing` degrades exponentially with the number of
steps.  This file proves that the degradation is an artifact of *forward*
tracking: for an **expanding** map the pseudo-orbit produced by a floating-point
execution is shadowed by a genuine orbit with an error bound
`δ / (λ - 1)` that is **uniform in the number of steps** — the classical
hyperbolic shadowing mechanism, made effective and combined with the
backward-error semantics of the arithmetic.

* `expanding_backward_shadowing` — the abstract theorem, proved by constructing
  the shadowing orbit backwards along inverse branches (a `1/λ`-contraction).
* `cubicExpand` / `cubic_inverse` — the concrete expanding polynomial map
  `p(z) = z³ + 2z`, whose global inverse branch is `1/2`-Lipschitz.
* `cubic_fl_shadowed_uniformly` — the composed theorem: any finite binary64
  execution of `p` staying within magnitude `B` is shadowed, uniformly in the
  number of steps, by an exact real orbit of `p`, with error at most
  `γ₈(u) (2B + B³)`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the exponential factor in the previous cycle's
logistic bound is not intrinsic to floating-point chaos; it is the price of
insisting that the shadowing orbit start at the *same* point.  Allowing the
initial condition to move should give an `O(u)` bound uniform in time.
Experiment (Experimenter): formalize backward construction along inverse
branches.  The induction is on the horizon `N`, shifting both the pseudo-orbit
and the branch family; the resulting error satisfies
`e_n ≤ (δ + e_{n+1})/λ`, whose fixed point is `δ/(λ-1)`.
Analysis (Analyst): the certificate consumed is exactly the one produced by the
semantics layer, confirming the modularity claim: no property of the arithmetic
beyond the local defect bound is used.
Critique (Critic): expansivity is essential — the logistic map at r = 4 has a
critical point and admits no globally `1/λ`-Lipschitz inverse branch, so the
theorem does not silently subsume the previous cycle's result.  The concrete
instantiation uses a genuinely expanding cubic, for which surjectivity (hence
existence of the branch) is proved from the intermediate-value theorem.
-- !-- End Lab Notes -- !--
-/

open Novelty.FloatBackwardError

open scoped BigOperators


/-! ### A concrete expanding polynomial dynamical system -/



lemma hornerR_cubicCoeffs (z : ℝ) : hornerR cubicCoeffs z = cubicExpand z := by
  simp [hornerR, cubicCoeffs, cubicExpand]; ring

/-- `p` expands distances by a factor at least `2`. -/
lemma cubicExpand_expansion (a b : ℝ) : 2 * |a - b| ≤ |cubicExpand a - cubicExpand b| := by
  have hfac : cubicExpand a - cubicExpand b = (a - b) * (a ^ 2 + a * b + b ^ 2 + 2) := by
    simp [cubicExpand]; ring
  have hpos : (2:ℝ) ≤ a ^ 2 + a * b + b ^ 2 + 2 := by nlinarith [sq_nonneg (a + b)]
  rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ a ^ 2 + a * b + b ^ 2 + 2)]
  have := abs_nonneg (a - b)
  nlinarith

lemma cubicExpand_injective : Function.Injective cubicExpand := by
  intro a b hab
  have := cubicExpand_expansion a b
  rw [hab] at this
  simp at this
  have : |a - b| ≤ 0 := by linarith
  have : a - b = 0 := by
    have h0 := abs_nonneg (a - b)
    have : |a - b| = 0 := le_antisymm this h0
    exact abs_eq_zero.mp this
  linarith



lemma cubicExpand_cubicInv (z : ℝ) : cubicExpand (cubicInv z) = z :=
  Function.surjInv_eq cubicExpand_surjective z

lemma cubicInv_cubicExpand (z : ℝ) : cubicInv (cubicExpand z) = z :=
  cubicExpand_injective (cubicExpand_cubicInv (cubicExpand z))

/-- The inverse branch is a `1/2`-contraction: this is the effective form of
expansivity consumed by the shadowing theorem. -/
lemma cubicInv_lipschitz (z w : ℝ) : |cubicInv z - cubicInv w| ≤ |z - w| / 2 := by
  have h := cubicExpand_expansion (cubicInv z) (cubicInv w)
  rw [cubicExpand_cubicInv, cubicExpand_cubicInv] at h
  linarith



open Novelty.FloatBackwardError in
theorem solution(M : RoundingModel) (x₀ B : ℝ) (N : ℕ)
    (hB : ∀ n ≤ N, |flOrbit M cubicCoeffs x₀ n| ≤ B) :
    ∃ y : ℕ → ℝ, (∀ n < N, cubicExpand (y n) = y (n + 1)) ∧
      (∀ n ≤ N, |y n - flOrbit M cubicCoeffs x₀ n|
        ≤ gamma M.u 8 * hornerAbs cubicCoeffs B) := by
  set δ := gamma M.u (2 * cubicCoeffs.length) * hornerAbs cubicCoeffs B with hδdef
  have hδ : 0 ≤ δ :=
    mul_nonneg (gamma_nonneg M.u_nonneg _) (hornerAbs_nonneg _ _)
  have hpo := flOrbit_isPseudoOrbit M cubicCoeffs x₀ B N hB
  have hfun : (fun z => hornerR cubicCoeffs z) = cubicExpand := by
    funext z; exact hornerR_cubicCoeffs z
  rw [hfun] at hpo
  obtain ⟨y, hy1, hy2⟩ :=
    expanding_backward_shadowing (f := cubicExpand) (g := fun _ => cubicInv)
      (lam := 2) hδ (by norm_num) (fun _ z => cubicExpand_cubicInv z)
      (fun _ z w => cubicInv_lipschitz z w)
      (fun n => cubicInv_cubicExpand _) N hpo
  refine ⟨y, hy1, ?_⟩
  intro n hn
  have := hy2 n hn
  have hlen : 2 * cubicCoeffs.length = 8 := by simp [cubicCoeffs]
  rw [hδdef, hlen, show (2:ℝ) - 1 = 1 by norm_num, div_one] at this
  exact this
