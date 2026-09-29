-- Prove2me | solution 1 for Novelty.FloatBackwardError.expanding_backward_shadowing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:07:28.196239+00:00
-- url     : https://prove2.me/submissions/167f4209-0bda-4a8f-ae71-43a3dcac7bbc

-- Sol generated from Novelty/FloatExpandingShadowing.lean
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatExpandingShadowing
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing

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













open Novelty.FloatBackwardError in
theorem solution{f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {lam δ : ℝ}
    (hδ : 0 ≤ δ) (hlam : 1 < lam)
    (hinv : ∀ n z, f (g n z) = z)
    (hlip : ∀ n z w, |g n z - g n w| ≤ |z - w| / lam)
    {x : ℕ → ℝ} (hfix : ∀ n, g n (f (x n)) = x n) (N : ℕ)
    (hpo : IsPseudoOrbit f δ x N) :
    ∃ y : ℕ → ℝ, (∀ n < N, f (y n) = y (n + 1)) ∧
      (∀ n ≤ N, |y n - x n| ≤ δ / (lam - 1)) := by
  have hlam0 : 0 < lam - 1 := by linarith
  have hbound_nonneg : 0 ≤ δ / (lam - 1) := div_nonneg hδ (le_of_lt hlam0)
  induction N generalizing x g with
  | zero =>
      refine ⟨fun _ => x 0, by omega, ?_⟩
      intro n hn
      interval_cases n
      simpa using hbound_nonneg
  | succ N ih =>
      obtain ⟨y', hy'orbit, hy'close⟩ :=
        ih (g := fun n => g (n + 1)) (x := fun n => x (n + 1))
          (fun n z => hinv (n + 1) z) (fun n z w => hlip (n + 1) z w)
          (fun n => hfix (n + 1)) (fun n hn => hpo (n + 1) (by omega))
      refine ⟨fun n => Nat.casesOn n (g 0 (y' 0)) (fun m => y' m), ?_, ?_⟩
      · intro n hn
        cases n with
        | zero => simpa using hinv 0 (y' 0)
        | succ m => exact hy'orbit m (by omega)
      · intro n hn
        cases n with
        | zero =>
            have h1 : |y' 0 - x 1| ≤ δ / (lam - 1) := hy'close 0 (Nat.zero_le _)
            have h2 : |x 1 - f (x 0)| ≤ δ := hpo 0 (by omega)
            have h3 : |g 0 (y' 0) - x 0| ≤ |y' 0 - f (x 0)| / lam := by
              have h3' := hlip 0 (y' 0) (f (x 0))
              rwa [hfix 0] at h3'
            have h4 : |y' 0 - f (x 0)| ≤ δ / (lam - 1) + δ := by
              have : |y' 0 - f (x 0)| ≤ |y' 0 - x 1| + |x 1 - f (x 0)| := by
                have hsplit : y' 0 - f (x 0) = (y' 0 - x 1) + (x 1 - f (x 0)) := by ring
                rw [hsplit]; exact abs_add_le _ _
              linarith
            have hfix' : (δ / (lam - 1) + δ) / lam = δ / (lam - 1) := by
              field_simp
              ring
            refine h3.trans ?_
            rw [← hfix']
            gcongr
        | succ m =>
            simpa using hy'close m (by omega)
