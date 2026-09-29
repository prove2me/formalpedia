-- Prove2me | solution 1 for Novelty.FloatBackwardError.variable_shadowing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:14:40.782628+00:00
-- url     : https://prove2.me/submissions/9ceb8acd-d404-4ea0-b704-7063218b0cb8

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





/-! ### The a-posteriori bound for a binary64 logistic execution -/





open Novelty.FloatBackwardError in
theorem solution{f : ℝ → ℝ} {δ : ℝ} {L : ℕ → ℝ} {S : Set ℝ}
    (hL : ∀ n, 0 ≤ L n) {x : ℕ → ℝ} {N : ℕ}
    (hLip : ∀ n < N, ∀ b ∈ S, |f (x n) - f b| ≤ L n * |x n - b|)
    (hy : ∀ n ≤ N, trueOrbit f (x 0) n ∈ S)
    (hpo : IsPseudoOrbit f δ x N) :
    ∀ n ≤ N, |x n - trueOrbit f (x 0) n| ≤ errBound δ L n := by
  intro n
  induction n with
  | zero => intro _; simp [trueOrbit, errBound]
  | succ n ih =>
      intro hn
      have hnN : n ≤ N := Nat.le_of_succ_le hn
      have hprev := ih hnN
      have hstep : |x (n + 1) - f (x n)| ≤ δ := hpo n hn
      have hlip : |f (x n) - f (trueOrbit f (x 0) n)| ≤ L n * |x n - trueOrbit f (x 0) n| :=
        hLip n hn _ (hy n hnN)
      have htri : |x (n + 1) - trueOrbit f (x 0) (n + 1)|
          ≤ |x (n + 1) - f (x n)| + |f (x n) - f (trueOrbit f (x 0) n)| := by
        have hsplit : x (n + 1) - trueOrbit f (x 0) (n + 1)
            = (x (n + 1) - f (x n)) + (f (x n) - f (trueOrbit f (x 0) n)) := by
          simp [trueOrbit]
        rw [hsplit]
        exact abs_add_le _ _
      have hmul : L n * |x n - trueOrbit f (x 0) n| ≤ L n * errBound δ L n :=
        mul_le_mul_of_nonneg_left hprev (hL n)
      simp only [errBound]
      linarith
