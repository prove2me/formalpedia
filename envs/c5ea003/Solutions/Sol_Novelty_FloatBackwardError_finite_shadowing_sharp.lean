-- Prove2me | solution 1 for Novelty.FloatBackwardError.finite_shadowing_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:13:07.059201+00:00
-- url     : https://prove2.me/submissions/b571342b-6e3b-47c6-8f96-63579e0f02b2

-- Sol generated from Novelty/FloatShadowingSharpness.lean
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing
import Definitions.Def_Novelty_FloatShadowingSharpness

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


lemma sharpWitness_eq (L δ : ℝ) (n : ℕ) :
    sharpWitness L δ n = δ * ∑ k ∈ Finset.range n, L ^ k := by
  induction n with
  | zero => simp [sharpWitness]
  | succ n ih =>
      have hgeom : (∑ k ∈ Finset.range (n + 1), L ^ k)
          = L * (∑ k ∈ Finset.range n, L ^ k) + 1 := geom_sum_succ
      simp only [sharpWitness, ih, hgeom]
      ring



/-! ### The a-posteriori bound for a binary64 logistic execution -/





open Novelty.FloatBackwardError in
theorem solution(L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ) :
    ∃ (f : ℝ → ℝ) (x : ℕ → ℝ),
      (∀ a b : ℝ, |f a - f b| = L * |a - b|) ∧
      (∀ n : ℕ, |x (n + 1) - f (x n)| = δ) ∧
      (∀ n : ℕ, |x n - trueOrbit f (x 0) n| = δ * ∑ k ∈ Finset.range n, L ^ k) := by
  refine ⟨fun z => L * z, sharpWitness L δ, ?_, ?_, ?_⟩
  · intro a b
    rw [show L * a - L * b = L * (a - b) by ring, abs_mul, abs_of_nonneg hL]
  · intro n
    have : sharpWitness L δ (n + 1) - L * sharpWitness L δ n = δ := by
      simp [sharpWitness]
    rw [this, abs_of_nonneg hδ]
  · intro n
    have hzero : ∀ m : ℕ, trueOrbit (fun z => L * z) (sharpWitness L δ 0) m = 0 := by
      intro m
      induction m with
      | zero => simp [trueOrbit, sharpWitness]
      | succ m ih => simp [trueOrbit, ih]
    rw [hzero n, sub_zero, sharpWitness_eq]
    have hsum : (0:ℝ) ≤ ∑ k ∈ Finset.range n, L ^ k :=
      Finset.sum_nonneg fun k _ => by positivity
    exact abs_of_nonneg (mul_nonneg hδ hsum)
