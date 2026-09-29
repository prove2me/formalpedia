-- Prove2me | solution 2 for Novelty.FloatBackwardError.hornerFl_forward_defect
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:38:25.164648+00:00
-- url     : https://prove2.me/submissions/edaa804a-5da7-401c-b046-20a40c90e227

import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner

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
section
open Novelty.FloatBackwardError
open scoped BigOperators

theorem solution (M : RoundingModel) (as : List ℝ) (x : ℝ) :
    |hornerFl M as x - hornerR as x| ≤ gamma M.u (2 * as.length) * hornerAbs as x := by
  first
  | exact Novelty.FloatBackwardError.hornerFl_forward_defect M as x
  | exact Novelty.FloatBackwardError.hornerFl_forward_defect
  | exact @Novelty.FloatBackwardError.hornerFl_forward_defect M as x
  | apply Novelty.FloatBackwardError.hornerFl_forward_defect
  | exact Novelty.FloatBackwardError.hornerFl_forward_defect ..


end
