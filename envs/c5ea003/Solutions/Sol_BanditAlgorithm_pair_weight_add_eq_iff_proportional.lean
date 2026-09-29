-- Prove2me | solution 1 for BanditAlgorithm.pair_weight_add_eq_iff_proportional
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T04:18:20.800623+00:00
-- url     : https://prove2.me/submissions/b3ea2525-3a57-4f0c-ab55-9eb705c3e1df

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The pairwise weight `xy/(x+y)`

Every quantity in the Track-and-Stop analysis that couples two arms is built from

  `pairHarm x y = xy/(x+y)`,

half the harmonic mean of `x` and `y`.  It appears as the effective sample size
of a pair: the generalised-likelihood-ratio statistic for "arm `a` beats arm `b`"
after `t` rounds is `pairHarm (T_a) (T_b) · (μ̂_a − μ̂_b)²/2`, and the optimal
allocation maximises `min_{j ≠ i*} pairHarm (α_{i*}) (α_j) · (μ_{i*} − μ_j)²/2`.
Both the rate lemmas and the continuity of the optimal allocation therefore rest
on the elementary properties of this one function.

## The junk value is the right value

At `x = y = 0` the formula reads `0/0`, which Lean evaluates to `0`.  That is not
a convention one has to work around — it is the correct value: `pairHarm x y ≤
min x y`, so the function extends continuously to the corner by `0`.  This is
what `continuousOn_pairHarm` says, and it is the reason the objective is
continuous on the *closed* simplex rather than only on its interior, which in
turn is what lets the maximum be attained.

That the corner is the only difficulty is worth stating plainly: away from
`x + y = 0` the function is a quotient with non-vanishing denominator and
continuity is automatic.  On the nonnegative quadrant `x + y = 0` forces
`x = y = 0`, so there is exactly one point to check by hand.

## Monotonicity

`pairHarm` is nondecreasing in each argument (`pairHarm_mono`).  Sampling an arm
more never decreases the evidence available about any pair containing it — which
is why lower bounds on the counts translate directly into lower bounds on the
GLR statistic.
-/

open Filter Topology Metric

namespace BanditAlgorithm

/-- `xy/(x+y)`, half the harmonic mean; `0` when both arguments vanish. -/
noncomputable def pairHarm (x y : ℝ) : ℝ := x * y / (x + y)

@[simp]
theorem pairHarm_zero_left (y : ℝ) : pairHarm 0 y = 0 := by simp [pairHarm]

@[simp]
theorem pairHarm_zero_right (x : ℝ) : pairHarm x 0 = 0 := by simp [pairHarm]

theorem pairHarm_comm (x y : ℝ) : pairHarm x y = pairHarm y x := by
  unfold pairHarm; rw [mul_comm, add_comm]

/-! ## Basic bounds -/

theorem pairHarm_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ pairHarm x y := by
  unfold pairHarm
  positivity

/-- `pairHarm x y ≤ x`: the pair is never more informative than its weaker half. -/
theorem pairHarm_le_left {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : pairHarm x y ≤ x := by
  rcases eq_or_lt_of_le (by linarith : (0 : ℝ) ≤ x + y) with hz | hpos
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [pairHarm, hx0, hy0]
  · unfold pairHarm
    rw [div_le_iff₀ hpos]
    nlinarith

theorem pairHarm_le_right {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : pairHarm x y ≤ y := by
  rw [pairHarm_comm]
  exact pairHarm_le_left hy hx

theorem pairHarm_le_min {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pairHarm x y ≤ min x y :=
  le_min (pairHarm_le_left hx hy) (pairHarm_le_right hx hy)

/-- The reciprocal form `1/pairHarm = 1/x + 1/y`, valid when both are positive. -/
theorem inv_pairHarm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (pairHarm x y)⁻¹ = x⁻¹ + y⁻¹ := by
  unfold pairHarm
  rw [inv_div]
  field_simp
  ring

theorem pairHarm_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < pairHarm x y := by
  unfold pairHarm
  positivity

/-! ## Monotonicity

Increasing either argument increases the weight.  The proof is the reciprocal
identity in disguise: `1/pairHarm = 1/x + 1/y` is decreasing in each variable. -/

theorem pairHarm_mono {x y x' y' : ℝ} (hx : 0 < x) (hy : 0 < y) (hxx : x ≤ x')
    (hyy : y ≤ y') : pairHarm x y ≤ pairHarm x' y' := by
  have hx' : 0 < x' := lt_of_lt_of_le hx hxx
  have hy' : 0 < y' := lt_of_lt_of_le hy hyy
  unfold pairHarm
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  -- `x'y'(x+y) − xy(x'+y') = x x'(y'−y) + y y'(x'−x) ≥ 0`
  nlinarith [mul_nonneg (mul_pos hx hx').le (sub_nonneg.mpr hyy),
    mul_nonneg (mul_pos hy hy').le (sub_nonneg.mpr hxx)]

/-! ## Continuity on the closed quadrant -/

theorem continuousAt_pairHarm_of_pos {p : ℝ × ℝ} (hp : 0 < p.1 + p.2) :
    ContinuousAt (fun q : ℝ × ℝ ↦ pairHarm q.1 q.2) p := by
  unfold pairHarm
  exact ContinuousAt.div (continuousAt_fst.mul continuousAt_snd)
    (continuousAt_fst.add continuousAt_snd) hp.ne'

/-- **`pairHarm` is continuous on the nonnegative quadrant**, corner included. -/
theorem continuousOn_pairHarm :
    ContinuousOn (fun q : ℝ × ℝ ↦ pairHarm q.1 q.2)
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := by
  rintro p ⟨hp1, hp2⟩
  rcases eq_or_lt_of_le (by linarith : (0 : ℝ) ≤ p.1 + p.2) with hz | hpos
  · -- the corner: squeeze against `min p.1 p.2`
    have hp10 : p.1 = 0 := by linarith
    have hp20 : p.2 = 0 := by linarith
    have hval : pairHarm p.1 p.2 = 0 := by simp [hp10]
    rw [ContinuousWithinAt, hval]
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε, hε, fun q hq hqd ↦ ?_⟩
    obtain ⟨hq1, hq2⟩ := hq
    have hle : pairHarm q.1 q.2 ≤ q.1 := pairHarm_le_left hq1 hq2
    have hnn : 0 ≤ pairHarm q.1 q.2 := pairHarm_nonneg hq1 hq2
    have hd : dist q p = max |q.1 - p.1| |q.2 - p.2| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    have hq1le : q.1 ≤ dist q p := by
      rw [hd, hp10]
      refine le_trans ?_ (le_max_left _ _)
      rw [sub_zero]
      exact le_abs_self _
    linarith
  · exact (continuousAt_pairHarm_of_pos hpos).continuousWithinAt

/-! ## The two-variable form used by the objective

The GLR rate for a pair is `pairHarm α_a α_b · (μ_a − μ_b)²/2`, jointly
continuous in the allocation and the means. -/

/-- The rate contributed by the pair `(a,b)` at allocation weights `(x,y)` and
mean gap `g`. -/
noncomputable def harmCost (x y g : ℝ) : ℝ := pairHarm x y * g ^ 2 / 2

theorem harmCost_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (g : ℝ) :
    0 ≤ harmCost x y g := by
  unfold harmCost
  have := pairHarm_nonneg hx hy
  positivity

theorem harmCost_mono {x y x' y' g : ℝ} (hx : 0 < x) (hy : 0 < y) (hxx : x ≤ x')
    (hyy : y ≤ y') : harmCost x y g ≤ harmCost x' y' g := by
  unfold harmCost
  have h := pairHarm_mono hx hy hxx hyy
  have : (0 : ℝ) ≤ g ^ 2 := sq_nonneg g
  gcongr

theorem continuousOn_harmCost :
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ ↦ harmCost q.1.1 q.1.2 q.2)
      {q : (ℝ × ℝ) × ℝ | 0 ≤ q.1.1 ∧ 0 ≤ q.1.2} := by
  unfold harmCost
  have hharm : ContinuousOn (fun q : (ℝ × ℝ) × ℝ ↦ pairHarm q.1.1 q.1.2)
      {q : (ℝ × ℝ) × ℝ | 0 ≤ q.1.1 ∧ 0 ≤ q.1.2} := by
    refine ContinuousOn.comp continuousOn_pairHarm continuous_fst.continuousOn ?_
    rintro q ⟨h1, h2⟩
    exact ⟨h1, h2⟩
  exact (hharm.mul (continuous_snd.pow 2).continuousOn).div_const 2

end BanditAlgorithm

/-!
# Strictness, superadditivity and the equality case for `pairHarm`

`Solutions/HarmonicPair.lean` collects the soft properties of `pairHarm x y =
xy/(x+y)`: nonnegativity, the bound by `min x y`, monotonicity, continuity on the
closed quadrant.  Uniqueness of the optimal allocation needs three sharper facts,
which are gathered here.

## 1. Strict monotonicity

`pairHarm x y < pairHarm x y'` for `0 < x` and `y < y'`.  Playing an arm more
*strictly* increases the evidence about every pair containing it, provided the
other arm of the pair is played at all.  This is what makes a maximiser of the
allocation objective equalise all its pair terms: an arm whose term is not
minimal can give up mass to those that are, strictly increasing the minimum.

## 2. A Lipschitz bound in the second argument

`pairHarm x y − pairHarm x (y − t) ≤ t` for `0 ≤ t ≤ y`.  The exact computation

  `pairHarm x y − pairHarm x (y−t) = t x²/((x+y)(x+y−t))`

shows the drop is at most `t`, since `x² ≤ (x+y)(x+y−t)`.  This is what makes
the perturbation argument quantitative: it names how small a transfer has to be
for the donating arm to stay above the old minimum, with no appeal to continuity
or to a compactness argument for the size of the step.

## 3. Superadditivity, with its equality case

  `pairHarm x₁ y₁ + pairHarm x₂ y₂ ≤ pairHarm (x₁+x₂) (y₁+y₂)`,

with equality **iff** `x₁ y₂ = x₂ y₁`, i.e. iff the two points lie on a common
ray through the origin.  Clearing denominators turns the difference into exactly
`(x₁y₂ − x₂y₁)²`, so both the inequality and its equality case come from a single
algebraic identity:

  `(x₁+x₂)(y₁+y₂)(x₁+y₁)(x₂+y₂) − [x₁y₁(x₂+y₂) + x₂y₂(x₁+y₁)](x₁+x₂+y₁+y₂)
     = (x₁y₂ − x₂y₁)²`.

Since `pairHarm` is positively homogeneous of degree one, superadditivity *is*
concavity, and the equality case says the concavity is strict in every direction
except along rays — which is the strongest form available, because homogeneity
makes `pairHarm` genuinely linear along each ray.  That is exactly the dichotomy
the uniqueness proof exploits: two distinct maximisers would have to be
proportional pair by pair, and two proportional points of the simplex are equal.
-/

namespace BanditAlgorithm

/-! ## Strict monotonicity -/

/-- **`pairHarm` is strictly increasing in its second argument** when the first
is positive. -/
theorem pairHarm_lt_of_lt_right {x y y' : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyy : y < y') :
    pairHarm x y < pairHarm x y' := by
  have hy' : 0 < y' := lt_of_le_of_lt hy hyy
  unfold pairHarm
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos (mul_pos hx hx) (sub_pos.mpr hyy)]

/-- The combined strict bound: increasing the second argument strictly, and the
first weakly, strictly increases the value. -/
theorem pairHarm_lt_of_le_of_lt {x x' y y' : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hxx : x ≤ x') (hyy : y < y') : pairHarm x y < pairHarm x' y' := by
  have hy' : 0 < y' := lt_of_le_of_lt hy hyy
  have hx' : 0 < x' := lt_of_lt_of_le hx hxx
  calc pairHarm x y < pairHarm x y' := pairHarm_lt_of_lt_right hx hy hyy
    _ ≤ pairHarm x' y' := pairHarm_mono hx hy' hxx le_rfl

/-! ## The Lipschitz bound -/

/-- **Reducing the second argument by `t` costs at most `t`.**  The exact drop is
`t x²/((x+y)(x+y−t))`, and `x² ≤ (x+y)(x+y−t)` whenever `t ≤ y`. -/
theorem pairHarm_sub_le {x y t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) (hty : t ≤ y) :
    pairHarm x y - t ≤ pairHarm x (y - t) := by
  have hy : 0 ≤ y := le_trans ht hty
  have hd1 : (0 : ℝ) < x + y := by linarith
  have hd2 : (0 : ℝ) < x + (y - t) := by linarith
  unfold pairHarm
  rw [sub_le_iff_le_add, div_add' _ _ _ hd2.ne', div_le_div_iff₀ hd1 hd2]
  -- the difference is `t x² ≥ 0` after clearing denominators
  nlinarith [mul_nonneg ht (sq_nonneg x), mul_nonneg (mul_nonneg ht hy) hy,
    mul_nonneg (mul_nonneg ht hx.le) hy]

/-! ## Homogeneity -/

/-- `pairHarm` is positively homogeneous of degree one. -/
theorem pairHarm_smul {c x y : ℝ} (hc : 0 ≤ c) :
    pairHarm (c * x) (c * y) = c * pairHarm x y := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · simp [← hc0]
  · unfold pairHarm
    rw [← mul_add]
    field_simp

/-! ## Superadditivity and its equality case -/

/-- The algebraic identity behind both the inequality and its equality case. -/
theorem pairHarm_add_key (x₁ y₁ x₂ y₂ : ℝ) :
    (x₁ + x₂) * (y₁ + y₂) * ((x₁ + y₁) * (x₂ + y₂))
        - (x₁ * y₁ * (x₂ + y₂) + x₂ * y₂ * (x₁ + y₁)) * ((x₁ + x₂) + (y₁ + y₂))
      = (x₁ * y₂ - x₂ * y₁) ^ 2 := by
  ring

/-- **Superadditivity.**  Merging two pairs is at least as informative as the
two separately. -/
theorem pairHarm_add_le {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁) (hy₁ : 0 < y₁)
    (hx₂ : 0 < x₂) (hy₂ : 0 < y₂) :
    pairHarm x₁ y₁ + pairHarm x₂ y₂ ≤ pairHarm (x₁ + x₂) (y₁ + y₂) := by
  have hd1 : (0 : ℝ) < x₁ + y₁ := by linarith
  have hd2 : (0 : ℝ) < x₂ + y₂ := by linarith
  have hd : (0 : ℝ) < (x₁ + x₂) + (y₁ + y₂) := by linarith
  unfold pairHarm
  rw [div_add_div _ _ hd1.ne' hd2.ne', div_le_div_iff₀ (by positivity) hd]
  nlinarith [sq_nonneg (x₁ * y₂ - x₂ * y₁), pairHarm_add_key x₁ y₁ x₂ y₂]

/-- **The equality case.**  Superadditivity is strict unless the two points are
proportional. -/
theorem pairHarm_add_eq_iff {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁) (hy₁ : 0 < y₁)
    (hx₂ : 0 < x₂) (hy₂ : 0 < y₂) :
    pairHarm x₁ y₁ + pairHarm x₂ y₂ = pairHarm (x₁ + x₂) (y₁ + y₂)
      ↔ x₁ * y₂ = x₂ * y₁ := by
  have hd1 : (0 : ℝ) < x₁ + y₁ := by linarith
  have hd2 : (0 : ℝ) < x₂ + y₂ := by linarith
  have hd : (0 : ℝ) < (x₁ + x₂) + (y₁ + y₂) := by linarith
  constructor
  · intro heq
    -- clearing denominators, the difference is `(x₁y₂ − x₂y₁)²`
    have hclear : (x₁ * y₁ * (x₂ + y₂) + x₂ * y₂ * (x₁ + y₁)) * ((x₁ + x₂) + (y₁ + y₂))
        = (x₁ + x₂) * (y₁ + y₂) * ((x₁ + y₁) * (x₂ + y₂)) := by
      unfold pairHarm at heq
      rw [div_add_div _ _ hd1.ne' hd2.ne', div_eq_div_iff (by positivity) hd.ne'] at heq
      linarith [heq]
    have hsq : (x₁ * y₂ - x₂ * y₁) ^ 2 = 0 := by
      rw [← pairHarm_add_key x₁ y₁ x₂ y₂]
      linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linarith
  · intro hprop
    have hclear : (x₁ * y₁ * (x₂ + y₂) + x₂ * y₂ * (x₁ + y₁)) * ((x₁ + x₂) + (y₁ + y₂))
        = (x₁ + x₂) * (y₁ + y₂) * ((x₁ + y₁) * (x₂ + y₂)) := by
      have := pairHarm_add_key x₁ y₁ x₂ y₂
      have hz : (x₁ * y₂ - x₂ * y₁) ^ 2 = 0 := by
        rw [hprop]; ring
      linarith
    unfold pairHarm
    rw [div_add_div _ _ hd1.ne' hd2.ne', div_eq_div_iff (by positivity) hd.ne']
    linarith

/-! ## The midpoint form

The form used by the uniqueness argument: the value at the midpoint of two
points dominates the average of the values, strictly unless the two points are
proportional. -/

theorem pairHarm_midpoint_le {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁) (hy₁ : 0 < y₁)
    (hx₂ : 0 < x₂) (hy₂ : 0 < y₂) :
    (pairHarm x₁ y₁ + pairHarm x₂ y₂) / 2
      ≤ pairHarm ((x₁ + x₂) / 2) ((y₁ + y₂) / 2) := by
  have hhalf : pairHarm ((x₁ + x₂) / 2) ((y₁ + y₂) / 2)
      = pairHarm (x₁ + x₂) (y₁ + y₂) / 2 := by
    have := pairHarm_smul (c := (1 : ℝ) / 2) (x := x₁ + x₂) (y := y₁ + y₂) (by norm_num)
    rw [show ((x₁ + x₂) / 2 : ℝ) = 1 / 2 * (x₁ + x₂) by ring,
      show ((y₁ + y₂) / 2 : ℝ) = 1 / 2 * (y₁ + y₂) by ring, this]
    ring
  rw [hhalf]
  have := pairHarm_add_le hx₁ hy₁ hx₂ hy₂
  linarith

/-- Equality at the midpoint forces proportionality. -/
theorem proportional_of_pairHarm_midpoint_eq {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁)
    (hy₁ : 0 < y₁) (hx₂ : 0 < x₂) (hy₂ : 0 < y₂)
    (heq : pairHarm ((x₁ + x₂) / 2) ((y₁ + y₂) / 2)
      ≤ (pairHarm x₁ y₁ + pairHarm x₂ y₂) / 2) :
    x₁ * y₂ = x₂ * y₁ := by
  have hhalf : pairHarm ((x₁ + x₂) / 2) ((y₁ + y₂) / 2)
      = pairHarm (x₁ + x₂) (y₁ + y₂) / 2 := by
    have := pairHarm_smul (c := (1 : ℝ) / 2) (x := x₁ + x₂) (y := y₁ + y₂) (by norm_num)
    rw [show ((x₁ + x₂) / 2 : ℝ) = 1 / 2 * (x₁ + x₂) by ring,
      show ((y₁ + y₂) / 2 : ℝ) = 1 / 2 * (y₁ + y₂) by ring, this]
    ring
  rw [hhalf] at heq
  have hle := pairHarm_add_le hx₁ hy₁ hx₂ hy₂
  have : pairHarm x₁ y₁ + pairHarm x₂ y₂ = pairHarm (x₁ + x₂) (y₁ + y₂) := by linarith
  exact (pairHarm_add_eq_iff hx₁ hy₁ hx₂ hy₂).mp this

end BanditAlgorithm

theorem _root_.solution {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁) (hy₁ : 0 < y₁)
    (hx₂ : 0 < x₂) (hy₂ : 0 < y₂) :
    (x₁ * y₁ / (x₁ + y₁) + x₂ * y₂ / (x₂ + y₂)
        = (x₁ + x₂) * (y₁ + y₂) / ((x₁ + x₂) + (y₁ + y₂)))
      ↔ x₁ * y₂ = x₂ * y₁ :=
  BanditAlgorithm.pairHarm_add_eq_iff hx₁ hy₁ hx₂ hy₂
