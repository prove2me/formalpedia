-- Prove2me | solution 1 for ProfileForm.powerProfile_of_scaleMultiplicative
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:39:21.704776+00:00
-- url     : https://prove2.me/submissions/da1f9bb3-cd00-4f05-a215-32a26a4933fe

-- Sol generated from NumberTheory/ProfileFormPowerLaw.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormPowerLaw

/-!
# Profile form: why the positional hit profile is a power law

Context (experiment 579, paper 229).  Re-analysis of `exp578_positions.npz`
(128 bit-length-96 semiprimes, 9594 recorded hits) fitted the small-`j` hit
profile `T` on the window `x ∈ [0, 2]` and found

* a **power law** `T(x) ≈ 0.0295 · (1 + x)^(-1.104)` with bootstrap CI
  `b ∈ [0.991, 1.218]` and Akaike weight `0.987`;
* the three rival one-dimensional families -- exponential (`ΔAICc +9.2`),
  logistic (`+11.5`, degenerate) and linear (`+16.9`) -- all lose.

This file isolates the *mathematics* behind that empirical verdict.  Nothing
here depends on the data: we prove that the power-law family is characterised
by an exact structural law, and that this structural law is incompatible with
each of the three rival families.

Main results.

* `powerProfile_scaleMul` — the power-law profile satisfies the *shift-scale
  multiplicativity* law
  `T 0 * T ((1+x)(1+y) - 1) = T x * T y`, i.e. it is multiplicative for the
  group law `x ⋆ y = (1+x)(1+y) - 1` on the shifted half-line.
* `powerProfile_of_scaleMultiplicative` — **rigidity**: *every* positive
  continuous profile obeying that law is a power law `A (1+x)^(-b)`.  This is
  the exact sense in which "the positional layer gets a law": the harmonic
  decline is forced, only the exponent is free.
* `powerProfile_exponent_unique` — the exponent is identifiable.
* `powerProfile_log_mid_strictConvex` — for `b > 0` the profile is *strictly*
  log-midpoint-convex: `T(t-h) · T(t+h) > T(t)^2`.
* `expProfile_log_mid_concave`, `logisticProfile_log_mid_concave`,
  `affineProfile_log_mid_concave` — each rival family satisfies the reverse
  inequality `f(t-h) · f(t+h) ≤ f(t)^2`.
* `powerProfile_ne_expProfile`, `powerProfile_ne_logisticProfile`,
  `powerProfile_ne_affineProfile` — hence a genuine power law (`b > 0`) is not
  a member of any of the three rival families: one single convexity invariant
  separates the winner from all three losers simultaneously.
* `declineFactor_bracket` — the window decline factor `T(0)/T(2) = 3^b` lies in
  `(2.8, 4.1)` for every `b` in the bootstrap interval `[0.991, 1.218]`,
  a bracket that contains the measured raw decline `3.25`.
-/

open ProfileForm

open Real

/-! ## The power-law profile and its structural law -/







/-! ## One convexity invariant separates the winner from all three losers

For a positive profile `f` put the *log-midpoint defect* at the three equally
spaced points `t - h < t < t + h`.  A power law with `b > 0` has
`f(t-h) f(t+h) > f(t)^2` (strict log-convexity), whereas exponential, logistic
and positive affine profiles all satisfy `f(t-h) f(t+h) ≤ f(t)^2`. -/








/-! ### Separation corollaries -/




/-! ## The window decline factor

Over the measured window `x ∈ [0,2]` the power law declines by the factor
`T(0)/T(2) = 3^b`.  We bracket it over the bootstrap interval for `b`. -/









open ProfileForm in
theorem solution(T : ℝ → ℝ)
    (hpos : ∀ x, -1 < x → 0 < T x)
    (hcont : ContinuousOn T (Set.Ioi (-1)))
    (hmul : ∀ x y, -1 < x → -1 < y →
      T 0 * T ((1 + x) * (1 + y) - 1) = T x * T y) :
    ∃ b : ℝ, ∀ x, -1 < x → T x = powerProfile (T 0) b x := by
  have hA : 0 < T 0 := hpos 0 (by norm_num)
  have hex : ∀ u : ℝ, -1 < Real.exp u - 1 := by
    intro u; have := Real.exp_pos u; linarith
  have hTpos : ∀ u : ℝ, 0 < T (Real.exp u - 1) := fun u => hpos _ (hex u)
  set g : ℝ → ℝ := fun u => Real.log (T (Real.exp u - 1) / T 0) with hg
  have hadd : ∀ u v, g (u + v) = g u + g v := by
    intro u v
    have h1 : (1 + (Real.exp u - 1)) * (1 + (Real.exp v - 1)) - 1
        = Real.exp (u + v) - 1 := by
      rw [Real.exp_add]; ring
    have h2 := hmul _ _ (hex u) (hex v)
    rw [h1] at h2
    have hEq : T (Real.exp (u + v) - 1) / T 0
        = (T (Real.exp u - 1) / T 0) * (T (Real.exp v - 1) / T 0) := by
      field_simp
      linarith [h2]
    simp only [hg, hEq]
    exact Real.log_mul (ne_of_gt (div_pos (hTpos u) hA))
      (ne_of_gt (div_pos (hTpos v) hA))
  have hcontg : Continuous g := by
    have h1 : Continuous fun u : ℝ => Real.exp u - 1 := by fun_prop
    have h2 : Continuous fun u : ℝ => T (Real.exp u - 1) :=
      hcont.comp_continuous h1 (fun u => Set.mem_Ioi.mpr (hex u))
    exact (h2.div_const (T 0)).log
      (fun u => ne_of_gt (div_pos (hTpos u) hA))
  have hlin : ∀ u : ℝ, g u = u * g 1 := by
    intro u
    have h := map_real_smul (AddMonoidHom.mk' g (fun u v => hadd u v)) hcontg u 1
    simpa [smul_eq_mul] using h
  refine ⟨-(g 1), fun x hx => ?_⟩
  have h1x : (0:ℝ) < 1 + x := by linarith
  have hTx : 0 < T x := hpos x hx
  have hux : Real.exp (Real.log (1 + x)) - 1 = x := by
    rw [Real.exp_log h1x]; ring
  have hgx : Real.log (T x / T 0) = Real.log (1 + x) * g 1 := by
    have h := hlin (Real.log (1 + x))
    simp only [hg, hux] at h
    exact h
  have hratio : T x / T 0 = Real.exp (Real.log (1 + x) * g 1) := by
    rw [← hgx, Real.exp_log (div_pos hTx hA)]
  have : T x = T 0 * Real.exp (Real.log (1 + x) * g 1) := by
    field_simp at hratio
    linarith [hratio]
  rw [this, powerProfile, Real.rpow_def_of_pos h1x]
  ring_nf
