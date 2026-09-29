-- Prove2me | Theorems.Thm_ProfileForm_powerProfile_of_scaleMultiplicative
-- name    : ProfileForm.powerProfile_of_scaleMultiplicative
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:37:56.916715+00:00
-- url     : https://prove2.me/theorems/3ced1dd2-4062-41e5-9afb-06caca22d8f3
-- title:
--   Rigidity of the profile form.
-- statement:
--   **Rigidity of the profile form.**  A positive, continuous profile on
--   `(-1, ∞)` that is multiplicative for the shift-scale group law is *necessarily*
--   a power law; the exponent is the only free parameter.
--
--   ```lean
--   theorem ProfileForm.powerProfile_of_scaleMultiplicative(T : ℝ → ℝ)
--       (hpos : ∀ x, -1 < x → 0 < T x)
--       (hcont : ContinuousOn T (Set.Ioi (-1)))
--       (hmul : ∀ x y, -1 < x → -1 < y →
--         T 0 * T ((1 + x) * (1 + y) - 1) = T x * T y) :
--       ∃ b : ℝ, ∀ x, -1 < x → T x = powerProfile (T 0) b x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ProfileFormPowerLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ProfileFormPowerLaw.lean#L75

-- Thm stub generated from NumberTheory/ProfileFormPowerLaw.lean
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

theorem ProfileForm.powerProfile_of_scaleMultiplicative(T : ℝ → ℝ)
    (hpos : ∀ x, -1 < x → 0 < T x)
    (hcont : ContinuousOn T (Set.Ioi (-1)))
    (hmul : ∀ x y, -1 < x → -1 < y →
      T 0 * T ((1 + x) * (1 + y) - 1) = T x * T y) :
    ∃ b : ℝ, ∀ x, -1 < x → T x = powerProfile (T 0) b x := by sorry
