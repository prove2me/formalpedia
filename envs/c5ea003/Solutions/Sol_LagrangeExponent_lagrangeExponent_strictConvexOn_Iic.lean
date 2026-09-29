-- Prove2me | solution 1 for LagrangeExponent.lagrangeExponent_strictConvexOn_Iic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:34:57.325973+00:00
-- url     : https://prove2.me/submissions/45fada02-27a1-4e5a-8b82-47e6bf6294eb

-- Sol generated from Novelty/LagrangeExponentConcavity.lean
import Mathlib
import Definitions.Def_Novelty_LagrangeExponentCore
import Theorems.Thm_LagrangeExponent_cbrt_neg
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





open LagrangeExponent in
theorem solution:
    StrictConvexOn ℝ (Set.Iic (1 / 27 : ℝ)) lagrangeExponent := by
  refine ⟨convex_Iic _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  simp only [mem_Iic] at hx hy
  simp only [smul_eq_mul]
  have hu : (0 : ℝ) ≤ 1 - 27 * x := by linarith
  have hv : (0 : ℝ) ≤ 1 - 27 * y := by linarith
  have hne : 1 - 27 * x ≠ 1 - 27 * y := by
    intro h; exact hxy (by linarith)
  have harg : 27 * (a * x + b * y) - 1 = -(a * (1 - 27 * x) + b * (1 - 27 * y)) := by
    have : a + b = 1 := hab
    nlinarith [this]
  have hmix : (0 : ℝ) ≤ a * (1 - 27 * x) + b * (1 - 27 * y) :=
    add_nonneg (mul_nonneg ha.le hu) (mul_nonneg hb.le hv)
  have key := (Real.strictConcaveOn_rpow (p := (1 : ℝ) / 3) (by norm_num) (by norm_num)).2
      (mem_Ici.2 hu) (mem_Ici.2 hv) hne ha hb hab
  simp only [smul_eq_mul] at key
  unfold lagrangeExponent
  have hx' : cbrt (27 * x - 1) = -((1 - 27 * x) ^ ((1 : ℝ) / 3)) := by
    have : (27 : ℝ) * x - 1 = -(1 - 27 * x) := by ring
    rw [this, cbrt_neg, cbrt_of_nonneg hu]
  have hy' : cbrt (27 * y - 1) = -((1 - 27 * y) ^ ((1 : ℝ) / 3)) := by
    have : (27 : ℝ) * y - 1 = -(1 - 27 * y) := by ring
    rw [this, cbrt_neg, cbrt_of_nonneg hv]
  rw [harg, cbrt_neg, cbrt_of_nonneg hmix, hx', hy']
  nlinarith [key, hab]
