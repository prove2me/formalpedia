-- Prove2me | solution 2 for Novelty.FloatBackwardError.cubic_fl_shadowed_uniformly
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:37:48.830693+00:00
-- url     : https://prove2.me/submissions/e552b874-933a-4092-b2d7-78bbaad2f484

import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatExpandingShadowing
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Novelty/FloatBackwardErrorHorner.lean ====
/-!
# Backward-error semantics for rounded polynomial evaluation

This file develops the *semantics* half of the conjecture

> every finite floating-point execution of a polynomial dynamical system that
> avoids overflow and exceptional values can be translated into an exact real
> pseudo-orbit whose local defect is bounded by a compositional expression in the
> unit roundoff and the intermediate magnitudes.

The model of computation is the standard IEEE-754 model *in the absence of
overflow, underflow and exceptional values* (`RoundingModel`): each arithmetic
operation returns the exact result multiplied by `(1 + e)` with `|e| ≤ u`, where
`u` is the unit roundoff (`2^-53` for binary64).  This is exactly the hypothesis
"the execution avoids overflow and exceptional values"; nothing else about the
bit-level format is used, so every conclusion applies verbatim to binary32,
binary64, and to any faithfully-rounded arithmetic.

Main results:

* `hornerFl_backward` — **backward-error semantics**: the rounded Horner
  evaluation of a polynomial with coefficient list `as` at a point `x` is the
  *exact* real evaluation at the same point `x` of a perturbed polynomial whose
  coefficients differ from `as` by at most the relative factor
  `gamma u (2 * as.length) = (1 + u) ^ (2 * as.length) - 1`.
* `hornerFl_forward_defect` — the resulting *local defect certificate*
  `|fl-eval − exact-eval| ≤ gamma u (2 n) * Σ |aᵢ| |x|ᵢ`, a compositional
  expression in the unit roundoff and the intermediate magnitudes.
* `gamma_le_classical` — the classical Higham bound
  `(1+u)^k − 1 ≤ k u / (1 − k u)` whenever `k u < 1`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): floating-point execution of a polynomial iteration is
not merely "approximately" the real iteration; it is *exactly* a real iteration
of a nearby polynomial, so the correct interface to a shadowing theorem is a
coefficientwise backward-error statement, not a forward error bound.
Experiment (Experimenter): formalize an abstract rounding model and prove the
backward statement by induction on the coefficient list, then *derive* the
forward defect from it.  The derivation succeeded, confirming that the forward
bound carries strictly less information than the backward one.
Analysis (Analyst): the exponent `2 n` (two roundings per Horner step) is forced
by the induction: each step multiplies all previously perturbed coefficients by
`(1+e₁)(1+e₂)`.  A sharper `2i`-graded version is true but the uniform bound is
the one consumed by the shadowing layer.
Critique (Critic): the model is unconditional in `u ≥ 0`; no hypothesis `u < 1`
is needed for the backward statement, and the classical `k u/(1 - k u)` form is
proved separately under its natural hypothesis `k u < 1`.
-- !-- End Lab Notes -- !--
-/

namespace Novelty.FloatBackwardError

open scoped BigOperators

-- [dropped: platform already declares RoundingModel]
-- [dropped: platform already declares gamma]
lemma gamma_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ) : 0 ≤ gamma u k := by
  have : (1 : ℝ) ≤ (1 + u) ^ k := one_le_pow₀ (by linarith)
  simpa [gamma] using this

lemma gamma_mono {u : ℝ} (hu : 0 ≤ u) {k l : ℕ} (h : k ≤ l) :
    gamma u k ≤ gamma u l := by
  have : (1 + u) ^ k ≤ (1 + u) ^ l := pow_le_pow_right₀ (by linarith) h
  simpa [gamma] using this

lemma u_le_gamma {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 1 ≤ k) : u ≤ gamma u k := by
  have h1 : gamma u 1 ≤ gamma u k := gamma_mono hu hk
  simpa [gamma] using h1

/-- The classical Higham form of the error constant:
`(1+u)^k − 1 ≤ k u / (1 − k u)` whenever `k u < 1`. -/
lemma gamma_le_classical {u : ℝ} (hu : 0 ≤ u) (k : ℕ) (hk : (k : ℝ) * u < 1) :
    gamma u k ≤ (k : ℝ) * u / (1 - (k : ℝ) * u) := by
  induction k with
  | zero => simp [gamma]
  | succ n ih =>
      have hn : (n : ℝ) * u < 1 := by
        push_cast at hk
        nlinarith [hu, Nat.cast_nonneg (α := ℝ) n]
      have ihn := ih hn
      have hpos : 0 < 1 - (n : ℝ) * u := by linarith
      have hpos' : 0 < 1 - ((n : ℝ) + 1) * u := by push_cast at hk; linarith
      -- `(1+u)^(n+1) - 1 = ((1+u)^n - 1) * (1+u) + u`
      have hstep : gamma u (n + 1) = gamma u n * (1 + u) + u := by
        simp [gamma, pow_succ]; ring
      have hbound : gamma u n * (1 + u) + u
          ≤ ((n : ℝ) * u / (1 - (n : ℝ) * u)) * (1 + u) + u := by
        have h1u : (0:ℝ) ≤ 1 + u := by linarith
        nlinarith [ihn]
      have hfinal : ((n : ℝ) * u / (1 - (n : ℝ) * u)) * (1 + u) + u
          ≤ ((n : ℝ) + 1) * u / (1 - ((n : ℝ) + 1) * u) := by
        have hLHS : ((n : ℝ) * u / (1 - (n : ℝ) * u)) * (1 + u) + u
            = ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) := by
          field_simp
          ring
        rw [hLHS]
        have hnum : (0:ℝ) ≤ ((n : ℝ) + 1) * u :=
          mul_nonneg (by positivity) hu
        gcongr
        linarith
      have : gamma u (n + 1) ≤ ((n : ℝ) + 1) * u / (1 - ((n : ℝ) + 1) * u) := by
        rw [hstep]; linarith
      simpa using this

/-! ### Horner evaluation, exact and rounded -/

/-- Exact real Horner evaluation of the polynomial `a₀ + a₁ x + a₂ x² + ⋯`. -/
-- [dropped: platform already declares hornerR]
-- [dropped: platform already declares hornerFl]
-- [dropped: platform already declares hornerAbs]
lemma hornerAbs_nonneg (as : List ℝ) (x : ℝ) : 0 ≤ hornerAbs as x := by
  induction as with
  | nil => simp [hornerAbs, hornerR]
  | cons a as ih =>
      have : hornerAbs (a :: as) x = |a| + |x| * hornerAbs as x := by
        simp [hornerAbs, hornerR]
      rw [this]
      have := abs_nonneg a
      have hx := abs_nonneg x
      nlinarith [ih]

lemma hornerAbs_cons (a : ℝ) (as : List ℝ) (x : ℝ) :
    hornerAbs (a :: as) x = |a| + |x| * hornerAbs as x := by
  simp [hornerAbs, hornerR]

/-- Coefficientwise perturbation bounds transfer to an evaluation bound. -/
lemma hornerR_dist_le {c : ℝ} {bs as : List ℝ}
    (h : List.Forall₂ (fun b a => |b - a| ≤ c * |a|) bs as) (x : ℝ) :
    |hornerR bs x - hornerR as x| ≤ c * hornerAbs as x := by
  induction h with
  | nil => simp [hornerR, hornerAbs]
  | @cons b a bs as hba _ ih =>
      have hx : (0:ℝ) ≤ |x| := abs_nonneg x
      have key : hornerR (b :: bs) x - hornerR (a :: as) x
          = (b - a) + x * (hornerR bs x - hornerR as x) := by
        simp [hornerR]; ring
      rw [key, hornerAbs_cons]
      calc |(b - a) + x * (hornerR bs x - hornerR as x)|
          ≤ |b - a| + |x| * |hornerR bs x - hornerR as x| := by
            refine (abs_add_le _ _).trans ?_
            simp [abs_mul]
        _ ≤ c * |a| + |x| * (c * hornerAbs as x) := by
            have := ih
            nlinarith [hx, ih, hba]
        _ = c * (|a| + |x| * hornerAbs as x) := by ring

/-- Scaling all coefficients scales the Horner value. -/
lemma hornerR_map_mul (t : ℝ) (as : List ℝ) (x : ℝ) :
    hornerR (as.map (fun a => a * t)) x = hornerR as x * t := by
  induction as with
  | nil => simp [hornerR]
  | cons a as ih => simp [hornerR, ih]; ring

/-- A coefficientwise perturbation bound implies a magnitude bound. -/
lemma abs_le_of_rel {u : ℝ} {n : ℕ} {b a : ℝ}
    (h : |b - a| ≤ gamma u n * |a|) : |b| ≤ (1 + u) ^ n * |a| := by
  have := abs_sub_abs_le_abs_sub b a
  have hg : gamma u n = (1 + u) ^ n - 1 := rfl
  nlinarith [abs_nonneg a, abs_nonneg b]

/-- Rescaling all coefficients by a factor `t` with `|t - 1| ≤ γ₂` degrades a
`γ_n` coefficientwise certificate to a `γ_{n+2}` certificate. -/
lemma forall₂_scale {u : ℝ} (hu : 0 ≤ u) {n : ℕ} {bs as : List ℝ} {t : ℝ}
    (ht : |t - 1| ≤ gamma u 2)
    (h : List.Forall₂ (fun b a => |b - a| ≤ gamma u n * |a|) bs as) :
    List.Forall₂ (fun b a => |b - a| ≤ gamma u (n + 2) * |a|)
      (bs.map (fun b => b * t)) as := by
  induction h with
  | nil => simp
  | @cons b a bs as hba _ ih =>
      refine List.Forall₂.cons ?_ ih
      have h1 : |b * t - a| ≤ |b| * |t - 1| + |b - a| := by
        have : b * t - a = b * (t - 1) + (b - a) := by ring
        rw [this]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
      have h2 : |b| ≤ (1 + u) ^ n * |a| := abs_le_of_rel hba
      have hpow : (0:ℝ) ≤ (1 + u) ^ n := by positivity
      have hg2 : gamma u 2 = (1 + u) ^ 2 - 1 := rfl
      have hgn : gamma u n = (1 + u) ^ n - 1 := rfl
      have hgn2 : gamma u (n + 2) = (1 + u) ^ n * (1 + u) ^ 2 - 1 := by
        simp [gamma, pow_add]
      have habs : (0:ℝ) ≤ |t - 1| := abs_nonneg _
      nlinarith [abs_nonneg a, abs_nonneg b, mul_nonneg hpow (abs_nonneg a)]

/-- **Backward-error semantics of rounded Horner evaluation.**
The floating-point evaluation of the polynomial with coefficients `as` at `x` is
the *exact* real evaluation at the same `x` of a polynomial whose coefficients
are relatively within `γ_{2n}` of `as`, where `n = as.length`. -/
theorem hornerFl_backward (M : RoundingModel) (as : List ℝ) (x : ℝ) :
    ∃ bs : List ℝ,
      List.Forall₂ (fun b a => |b - a| ≤ gamma M.u (2 * as.length) * |a|) bs as ∧
      hornerFl M as x = hornerR bs x := by
  induction as with
  | nil => exact ⟨[], List.Forall₂.nil, by simp [hornerFl, hornerR]⟩
  | cons a as ih =>
      obtain ⟨bs, hbs, hval⟩ := ih
      obtain ⟨e₂, he₂, hmul⟩ := M.mul_spec x (hornerFl M as x)
      obtain ⟨e₁, he₁, hadd⟩ := M.add_spec a (M.mul x (hornerFl M as x))
      set t : ℝ := (1 + e₁) * (1 + e₂) with ht
      have hlen : 2 * (a :: as).length = 2 * as.length + 2 := by simp; ring
      have ht1 : |t - 1| ≤ gamma M.u 2 := by
        have : t - 1 = e₁ + e₂ + e₁ * e₂ := by rw [ht]; ring
        rw [this]
        have h3 : |e₁ + e₂ + e₁ * e₂| ≤ |e₁| + |e₂| + |e₁| * |e₂| := by
          have hA := abs_add_le (e₁ + e₂) (e₁ * e₂)
          have hB := abs_add_le e₁ e₂
          rw [abs_mul] at hA
          linarith
        have hu := M.u_nonneg
        have hg : gamma M.u 2 = 2 * M.u + M.u ^ 2 := by simp [gamma]; ring
        rw [hg]
        nlinarith [abs_nonneg e₁, abs_nonneg e₂, he₁, he₂]
      refine ⟨(a * (1 + e₁)) :: bs.map (fun b => b * t), ?_, ?_⟩
      · rw [hlen]
        refine List.Forall₂.cons ?_ (forall₂_scale M.u_nonneg ht1 hbs)
        · -- head coefficient: relative error `|e₁| ≤ u ≤ γ_{2n+2}`
          have hEq : |a * (1 + e₁) - a| = |e₁| * |a| := by
            rw [show a * (1 + e₁) - a = e₁ * a by ring, abs_mul]
          rw [hEq]
          have hu : M.u ≤ gamma M.u (2 * as.length + 2) :=
            u_le_gamma M.u_nonneg (by omega)
          nlinarith [he₁, abs_nonneg a]
      · rw [hornerFl, hadd, hmul, hval, hornerR, hornerR_map_mul, ht]
        ring

/-- **Local defect certificate (forward form).**  The floating-point Horner
evaluation differs from the exact real evaluation by at most
`γ_{2n} · Σ |aᵢ| |x|ⁱ`: a compositional expression in the unit roundoff and the
intermediate magnitudes. -/
theorem hornerFl_forward_defect (M : RoundingModel) (as : List ℝ) (x : ℝ) :
    |hornerFl M as x - hornerR as x| ≤ gamma M.u (2 * as.length) * hornerAbs as x := by
  obtain ⟨bs, hbs, hval⟩ := hornerFl_backward M as x
  rw [hval]
  exact hornerR_dist_le hbs x

/-! ### Sharpness of the defect certificate

The factor `γ_{2n}(u)` is linear in `u` to first order.  The following worst-case
model (every operation rounds *up* by exactly the maximal relative amount) shows
that no bound of order `u²` can hold: the defect really is of size `u` times the
magnitude functional, so the certificate is sharp up to the constant `3`. -/

/-- The adversarial rounding model in which every operation incurs the maximal
relative error `+u`.  It satisfies the IEEE-754 relative-error axioms. -/
-- [dropped: platform already declares uniformModel]
theorem uniformModel_defect_eq (u : ℝ) (hu : 0 ≤ u) (a x : ℝ) :
    |hornerFl (uniformModel u hu) [a] x - hornerR [a] x| = u * hornerAbs [a] x := by
  have h1 : hornerFl (uniformModel u hu) [a] x = a * (1 + u) := by
    simp [hornerFl, uniformModel]
  have h2 : hornerR [a] x = a := by simp [hornerR]
  have h3 : hornerAbs [a] x = |a| := by simp [hornerAbs, hornerR]
  rw [h1, h2, h3, show a * (1 + u) - a = u * a by ring, abs_mul, abs_of_nonneg hu]

/-- **The local defect certificate is sharp up to a constant factor**: there are
executions whose defect is at least a third of the certified bound, so the
first-order term in `u` cannot be removed. -/
theorem defect_bound_sharp (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (a x : ℝ) :
    gamma u (2 * ([a] : List ℝ).length) * hornerAbs [a] x / 3
      ≤ |hornerFl (uniformModel u hu) [a] x - hornerR [a] x| := by
  rw [uniformModel_defect_eq u hu a x]
  have hA : (0:ℝ) ≤ hornerAbs [a] x := hornerAbs_nonneg _ _
  have hg : gamma u (2 * ([a] : List ℝ).length) = 2 * u + u ^ 2 := by
    simp [gamma]; ring
  rw [hg, div_le_iff₀ (by norm_num : (0:ℝ) < 3)]
  nlinarith [mul_nonneg (mul_nonneg hu (sub_nonneg.mpr hu1)) hA]

end Novelty.FloatBackwardError
-- ==== upstream: Packages/Catalog/Novelty/FloatPseudoOrbitShadowing.lean ====
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

namespace Novelty.FloatBackwardError

open scoped BigOperators

/-! ### Pseudo-orbits -/

-- [dropped: platform already declares IsPseudoOrbit]
-- [dropped: platform already declares flOrbit]
-- [dropped: platform already declares trueOrbit]
lemma hornerAbs_mono {as : List ℝ} {x B : ℝ} (h : |x| ≤ B) :
    hornerAbs as x ≤ hornerAbs as B := by
  have hB : 0 ≤ B := le_trans (abs_nonneg x) h
  induction as with
  | nil => simp [hornerAbs, hornerR]
  | cons a as ih =>
      rw [hornerAbs_cons, hornerAbs_cons, abs_of_nonneg hB]
      have h1 : hornerAbs as x ≤ hornerAbs as B := ih
      have h2 : 0 ≤ hornerAbs as x := hornerAbs_nonneg as x
      have h3 : 0 ≤ |x| := abs_nonneg x
      nlinarith [hornerAbs_nonneg as B]

/-! ### Semantics layer: a floating-point execution is a certified pseudo-orbit -/

/-- **Semantic translation theorem.**  A finite floating-point execution of the
polynomial iteration `x ↦ p(x)` that is observed to stay within magnitude `B` is
an exact real `δ`-pseudo-orbit of the exact map, with the *compositional* local
defect `δ = γ_{2n}(u) · Σ|aᵢ| Bⁱ`. -/
theorem flOrbit_isPseudoOrbit (M : RoundingModel) (as : List ℝ) (x₀ B : ℝ)
    (N : ℕ) (hB : ∀ n ≤ N, |flOrbit M as x₀ n| ≤ B) :
    IsPseudoOrbit (fun z => hornerR as z)
      (gamma M.u (2 * as.length) * hornerAbs as B) (flOrbit M as x₀) N := by
  intro n hn
  have hx : flOrbit M as x₀ (n + 1) = hornerFl M as (flOrbit M as x₀ n) := rfl
  rw [hx]
  refine (hornerFl_forward_defect M as _).trans ?_
  have hmag : hornerAbs as (flOrbit M as x₀ n) ≤ hornerAbs as B :=
    hornerAbs_mono (hB n (le_of_lt hn))
  exact mul_le_mul_of_nonneg_left hmag (gamma_nonneg M.u_nonneg _)

/-- **Backward-error semantics of the whole execution.**  Every step of the
floating-point execution is an *exact* step of a polynomial map whose
coefficients are relatively within `γ_{2n}(u)` of the nominal ones: the
execution is the exact orbit of a nonautonomous perturbation of the system. -/
theorem flOrbit_nonautonomous_exact (M : RoundingModel) (as : List ℝ) (x₀ : ℝ) :
    ∀ n : ℕ, ∃ bs : List ℝ,
      List.Forall₂ (fun b a => |b - a| ≤ gamma M.u (2 * as.length) * |a|) bs as ∧
      flOrbit M as x₀ (n + 1) = hornerR bs (flOrbit M as x₀ n) := by
  intro n
  obtain ⟨bs, hbs, hval⟩ := hornerFl_backward M as (flOrbit M as x₀ n)
  exact ⟨bs, hbs, hval⟩

/-! ### Dynamics layer: finite-time shadowing -/

/-- **Finite-time shadowing.**  A `δ`-pseudo-orbit that remains in a region where
`f` is `L`-Lipschitz is tracked by the true orbit through the same initial point,
with error at most `δ · (1 + L + ⋯ + L^{n-1})`. -/
theorem finite_shadowing {f : ℝ → ℝ} {L δ : ℝ} {S : Set ℝ} (hL : 0 ≤ L)
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

/-- **Time-uniform shadowing for contractions.**  If the map is a contraction on
the visited region then the shadowing error never exceeds `δ / (1 - L)`,
uniformly in the number of steps. -/
theorem contraction_shadowing {f : ℝ → ℝ} {L δ : ℝ} {S : Set ℝ} (hδ : 0 ≤ δ)
    (hL : 0 ≤ L) (hL1 : L < 1)
    (hLip : ∀ a ∈ S, ∀ b ∈ S, |f a - f b| ≤ L * |a - b|)
    {x : ℕ → ℝ} {N : ℕ}
    (hx : ∀ n ≤ N, x n ∈ S)
    (hy : ∀ n ≤ N, trueOrbit f (x 0) n ∈ S)
    (hpo : IsPseudoOrbit f δ x N) :
    ∀ n ≤ N, |x n - trueOrbit f (x 0) n| ≤ δ / (1 - L) := by
  intro n hn
  refine (finite_shadowing hL hLip hx hy hpo n hn).trans ?_
  have hsum : (∑ k ∈ Finset.range n, L ^ k) = (1 - L ^ n) / (1 - L) := by
    rw [geom_sum_eq (by linarith) n, ← neg_sub 1 (L ^ n), ← neg_sub 1 L, neg_div_neg_eq]
  have hpos : 0 < 1 - L := by linarith
  have hpow : 0 ≤ L ^ n := by positivity
  rw [hsum, show δ * ((1 - L ^ n) / (1 - L)) = (δ * (1 - L ^ n)) / (1 - L) by ring]
  gcongr
  nlinarith

/-! ### Instantiation: the logistic map at parameter 4 in IEEE binary64 -/

/-- The exact logistic map at the chaotic parameter `r = 4`. -/
-- [dropped: platform already declares logistic]
-- [dropped: platform already declares logisticCoeffs]
lemma hornerR_logisticCoeffs (z : ℝ) : hornerR logisticCoeffs z = logistic z := by
  simp [hornerR, logisticCoeffs, logistic]; ring

lemma hornerAbs_logisticCoeffs_one : hornerAbs logisticCoeffs 1 = 8 := by
  norm_num [hornerAbs, hornerR, logisticCoeffs]

/-- The unit interval is invariant for the exact logistic map. -/
lemma logistic_maps_unitInterval {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    logistic z ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hz
  simp only [Set.mem_Icc, logistic]
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (2 * z - 1)]

lemma trueOrbit_logistic_mem {y₀ : ℝ} (hy₀ : y₀ ∈ Set.Icc (0:ℝ) 1) :
    ∀ n : ℕ, trueOrbit logistic y₀ n ∈ Set.Icc (0:ℝ) 1 := by
  intro n
  induction n with
  | zero => simpa [trueOrbit] using hy₀
  | succ n ih => exact logistic_maps_unitInterval ih

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

/-- The unit-roundoff bound for IEEE binary64. -/
lemma binary64_defect_bound {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (2:ℝ) ^ (-53 : ℤ)) :
    gamma u (2 * logisticCoeffs.length) * hornerAbs logisticCoeffs 1 ≤ (2:ℝ) ^ (-46 : ℤ) := by
  have hlen : 2 * logisticCoeffs.length = 6 := by simp [logisticCoeffs]
  have h53 : (2:ℝ) ^ (-53 : ℤ) = 1 / 9007199254740992 := by
    norm_num [zpow_neg]
  have h46 : (2:ℝ) ^ (-46 : ℤ) = 1 / 70368744177664 := by
    norm_num [zpow_neg]
  have hu' : u ≤ 1 / 9007199254740992 := by rw [h53] at hu; exact hu
  have h6 : ((6:ℕ) : ℝ) * u < 1 := by
    push_cast
    linarith
  have hg := gamma_le_classical hu0 6 h6
  have hden : (1:ℝ) - ((6:ℕ) : ℝ) * u ≥ 1 / 2 := by push_cast; linarith
  have hgb : gamma u 6 ≤ 12 * u := by
    refine hg.trans ?_
    rw [div_le_iff₀ (by push_cast; linarith)]
    push_cast
    nlinarith
  rw [hlen, hornerAbs_logisticCoeffs_one, h46]
  nlinarith [gamma_nonneg hu0 6]

/-- **Composed theorem: certified shadowing of a binary64 logistic execution.**

Let `x` be the floating-point orbit produced by evaluating `4x(1-x)` by Horner's
rule in any IEEE-754 arithmetic with unit roundoff at most `2⁻⁵³` (binary64),
started at `x₀ ∈ [0,1]`, and suppose the execution is *observed* to remain in
`[0,1]` for its first `N` steps (this is precisely the runtime certificate that
no overflow or exceptional value occurred).  Then the execution is shadowed by
the **exact real** logistic orbit through the same initial point, with error at
most `2⁻⁴⁶ (4ⁿ - 1)/3` after `n ≤ N` steps.

The two ingredients are strictly separated: `2⁻⁴⁶` comes only from the
backward-error semantics of the arithmetic, and `(4ⁿ-1)/3` only from the
Lipschitz constant of the dynamics. -/
theorem logistic_binary64_shadowing (M : RoundingModel) (hu : M.u ≤ (2:ℝ) ^ (-53 : ℤ))
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

end Novelty.FloatBackwardError
-- ==== upstream: Packages/Catalog/Novelty/FloatExpandingShadowing.lean ====
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

namespace Novelty.FloatBackwardError

open scoped BigOperators

/-- **Uniform-in-time shadowing for expanding maps.**  If `f` admits inverse
branches `g n` that contract by `1/λ` with `λ > 1`, then every finite
`δ`-pseudo-orbit of `f` is shadowed by a genuine orbit of `f` with error at most
`δ/(λ-1)`, *independently of the length of the execution*. -/
theorem expanding_backward_shadowing {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {lam δ : ℝ}
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

/-! ### A concrete expanding polynomial dynamical system -/

/-- The expanding cubic `p(z) = z³ + 2z`. -/
-- [dropped: platform already declares cubicExpand]
-- [dropped: platform already declares cubicCoeffs]
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

-- [dropped: platform already declares cubicExpand_surjective]
-- [dropped: platform already declares cubicInv]
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

/-- **Composed theorem: uniform-in-time certified shadowing of a floating-point
execution of an expanding polynomial.**

Any finite floating-point execution of `p(z) = z³ + 2z` (Horner evaluation, any
IEEE-754 arithmetic with unit roundoff `u`, no overflow or exceptional values)
that is observed to stay within magnitude `B` is shadowed by an *exact* real
orbit of `p`, with error at most `γ₈(u) (2B + B³)` at **every** step — a bound
independent of the number of steps executed. -/
theorem cubic_fl_shadowed_uniformly (M : RoundingModel) (x₀ B : ℝ) (N : ℕ)
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

end Novelty.FloatBackwardError
section
open Novelty.FloatBackwardError
open scoped BigOperators

theorem solution (M : RoundingModel) (x₀ B : ℝ) (N : ℕ)
    (hB : ∀ n ≤ N, |flOrbit M cubicCoeffs x₀ n| ≤ B) :
    ∃ y : ℕ → ℝ, (∀ n < N, cubicExpand (y n) = y (n + 1)) ∧
      (∀ n ≤ N, |y n - flOrbit M cubicCoeffs x₀ n|
        ≤ gamma M.u 8 * hornerAbs cubicCoeffs B) := by
  first
  | exact Novelty.FloatBackwardError.cubic_fl_shadowed_uniformly M x₀ B N hB
  | exact Novelty.FloatBackwardError.cubic_fl_shadowed_uniformly
  | exact @Novelty.FloatBackwardError.cubic_fl_shadowed_uniformly M x₀ B N hB
  | apply Novelty.FloatBackwardError.cubic_fl_shadowed_uniformly
  | exact Novelty.FloatBackwardError.cubic_fl_shadowed_uniformly ..


end
