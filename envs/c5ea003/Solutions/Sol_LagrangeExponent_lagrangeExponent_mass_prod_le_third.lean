-- Prove2me | solution 1 for LagrangeExponent.lagrangeExponent_mass_prod_le_third
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:33:31.46741+00:00
-- url     : https://prove2.me/submissions/2bf2e0ae-997f-4e01-a701-8c06a4753635

-- Sol generated from Novelty/LagrangeExponentConcavity.lean
import Mathlib
import Definitions.Def_Novelty_LagrangeExponentCore
import Theorems.Thm_LagrangeExponent_lagrangeExponent_critical
/-
# Concavity of the Lagrange exponent on the physical range `[1/27, ∞)`

Building on `Novelty.LagrangeExponentCore`, where the **Lagrange exponent**

  `σ t = (1 + ∛(27 t - 1)) / 3`

was introduced as the inverse of the critical cubic `h y = y³ - y² + y/3`
(`h y = ((3y-1)³ + 1)/27`), this file proves the main structural theorem of the
programme and pins down its exact boundary.

## Main results

* `lagrangeExponent_concaveOn` — `σ` is concave on `Set.Ici (1/27)`;
* `lagrangeExponent_strictConcaveOn` — in fact *strictly* concave there;
* `lagrangeExponent_midpoint_concave` — the midpoint form: averaging two masses
  never decreases the growth rate, `(σ s + σ t)/2 ≤ σ ((s+t)/2)`;
* `lagrangeExponent_jensen` — the finite Jensen form for an arbitrary weighted
  average of masses;
* `lagrangeExponent_strictConvexOn_Iic` — below the critical mass the behaviour is
  *reversed*: `σ` is strictly convex on `Set.Iic (1/27)`;
* `lagrangeExponent_not_concaveOn_Ici` — consequently `1/27` is the **exact**
  threshold: for every `a < 1/27`, `σ` fails to be concave on `Set.Ici a`.
  (Adversarial check: the theorem is not vacuously "concave everywhere".)
* `lagrangeExponent_hasDerivAt` — the derivative `σ' t = 3 (27t-1)^(-2/3)` above the
  critical mass, together with `lagrangeExponent_deriv_antitoneOn`, the analytic
  shadow of concavity.
* `three_mass_prod_le_inv27` / `lagrangeExponent_mass_prod_le_third` — the bridge to
  mass distributions: by AM–GM a three–point distribution has product at most `1/27`,
  which is precisely the critical mass, so `1/27` is not an arbitrary constant.

## Structure of the proof

Because `h' y = 3 (y - 1/3)²` vanishes only at `y = 1/3`, the cubic is an affine shift
of a pure cube and `σ` is an affine shift of `x ↦ x^(1/3)`.  Concavity on
`[1/27, ∞)` is therefore the concavity of `x ↦ x^(1/3)` on `[0, ∞)` transported by the
increasing affine change of variables `t ↦ 27 t - 1`; convexity on `(-∞, 1/27]` is the
same statement transported by the *decreasing* affine map `t ↦ 1 - 27 t`, whose sign flip
reverses the inequality.  The inflection at `t = 1/27` is exactly the image of the
degenerate critical point `y = 1/3`.
-/

open LagrangeExponent

open Set

/-! ## Concavity above the critical mass -/






/-! ## Convexity below the critical mass, and sharpness of the threshold -/






/-! ## The analytic shadow: the derivative above the critical mass -/



/-! ## Bridge to mass distributions: why `1/27` -/

/-- AM–GM in three variables: a probability vector on three states has product at most
`1/27`, attained only at the uniform distribution. -/
theorem three_mass_prod_le_inv27 {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h : p + q + r = 1) : p * q * r ≤ 1 / 27 := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r), sq_nonneg (p + q - 2 * r),
    mul_nonneg hp hq, mul_nonneg hq hr, mul_nonneg hp hr]




open LagrangeExponent in
theorem solution{p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h : p + q + r = 1) : lagrangeExponent (p * q * r) ≤ 1 / 3 := by
  have := three_mass_prod_le_inv27 hp hq hr h
  calc lagrangeExponent (p * q * r) ≤ lagrangeExponent (1 / 27) :=
        lagrangeExponent_strictMono.monotone this
    _ = 1 / 3 := lagrangeExponent_critical
