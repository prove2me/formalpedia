-- Prove2me | solution 1 for RLHF.l1_drift_lower_mad
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:19:01.116986+00:00
-- url     : https://prove2.me/submissions/e6dba930-bf01-4310-9959-ca65bcff14ab

import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Algebra/RLHFDriftCore.lean ====
/-!
# Core objects of the RLHF alignment-drift catalogue

Domain: Algebra (convex analysis × information theory × alignment theory).

This file collects the base objects that the RLHF drift thread of the catalogue is
phrased in — finite probability vectors, the Gibbs (KL-regularised) policy, the
Kullback–Leibler divergence, the total-variation (`ℓ¹`) distance, and the first two
moment functionals of a reward — together with the elementary API used downstream.

The names and definitions follow the conventions of the RLHF drift files of the
catalogue (`RLHF.IsDist`, `RLHF.gibbsPolicy`, `RLHF.klDiv`, `RLHF.l1Dist`,
`RLHF.rewardRange`, `RLHF.mean`, `RLHF.variance`, ...), so the results proved here and
in `Algebra.RLHFMeanAbsoluteDeviation` / `Algebra.RLHFKLSecondOrder` speak about
exactly the same objects as `RLHF.kl_gibbs_le_variance` and
`RLHF.gibbs_l1_le_variance`.

Nothing in this file is deep; it exists so that the two research files that follow are
self-contained and compile.
-/

namespace RLHF

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## 1. Finite probability vectors -/

-- [dropped: platform already declares IsDist]
-- [dropped: platform already declares IsPosDist]
theorem IsPosDist.isDist {p : Ω → ℝ} (hp : IsPosDist p) : IsDist p :=
  ⟨fun y => (hp.pos y).le, hp.total⟩

/-! ## 2. Moment functionals -/

/-- The mean `𝔼_p[f] = ∑ y, p y · f y`. -/
-- [dropped: platform already declares mean]
-- [dropped: platform already declares variance]
-- [dropped: platform already declares mad]
-- [dropped: platform already declares cov]
theorem variance_nonneg {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) : 0 ≤ variance p f :=
  Finset.sum_nonneg fun y _ => mul_nonneg (hp.nonneg y) (sq_nonneg _)

theorem mad_nonneg {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) : 0 ≤ mad p f :=
  Finset.sum_nonneg fun y _ => mul_nonneg (hp.nonneg y) (abs_nonneg _)

/-- The centred first moment vanishes. -/
theorem sum_centered {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) :
    ∑ y, p y * (f y - mean p f) = 0 := by
  have h : ∀ y, p y * (f y - mean p f) = p y * f y - mean p f * p y := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.total]
  simp [mean]

/-- The expectation of a constant. -/
theorem sum_const_dist {p : Ω → ℝ} (hp : IsDist p) (c : ℝ) : ∑ _y : Ω, p _y * c = c := by
  rw [← Finset.sum_mul, hp.total, one_mul]

/-! ## 3. The Gibbs policy -/

/-- The partition function `Z_β = ∑ y, p y e^{r y / β}`. -/
-- [dropped: platform already declares partition]
-- [dropped: platform already declares gibbsPolicy]
-- [dropped: platform already declares klDiv]
-- [dropped: platform already declares l1Dist]
theorem l1Dist_nonneg (q p : Ω → ℝ) : 0 ≤ l1Dist q p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

variable [Nonempty Ω]

-- [dropped: platform already declares rewardRange]
theorem partition_pos {β : ℝ} {r p : Ω → ℝ} (hp : IsPosDist p) : 0 < partition β r p :=
  Finset.sum_pos (fun y _ => mul_pos (hp.pos y) (Real.exp_pos _)) univ_nonempty

theorem mean_le_sup {p r : Ω → ℝ} (hp : IsDist p) : mean p r ≤ univ.sup' univ_nonempty r := by
  have h : ∀ y ∈ (univ : Finset Ω), p y * r y ≤ p y * univ.sup' univ_nonempty r :=
    fun y _ => mul_le_mul_of_nonneg_left (Finset.le_sup' r (mem_univ y)) (hp.nonneg y)
  have := Finset.sum_le_sum h
  rwa [← Finset.sum_mul, hp.total, one_mul] at this

theorem inf_le_mean {p r : Ω → ℝ} (hp : IsDist p) : univ.inf' univ_nonempty r ≤ mean p r := by
  have h : ∀ y ∈ (univ : Finset Ω), p y * univ.inf' univ_nonempty r ≤ p y * r y :=
    fun y _ => mul_le_mul_of_nonneg_left (Finset.inf'_le r (mem_univ y)) (hp.nonneg y)
  have := Finset.sum_le_sum h
  rwa [← Finset.sum_mul, hp.total, one_mul] at this

theorem rewardRange_nonneg (r : Ω → ℝ) : 0 ≤ rewardRange r := by
  obtain ⟨y⟩ := ‹Nonempty Ω›
  have h1 : r y ≤ univ.sup' univ_nonempty r := Finset.le_sup' r (mem_univ y)
  have h2 : univ.inf' univ_nonempty r ≤ r y := Finset.inf'_le r (mem_univ y)
  simp only [rewardRange]; linarith

omit [Nonempty Ω] in
/-- The mean minimises the mean square deviation: `Var_p(f) ≤ 𝔼_p[(f − c)²]` for every
centre `c`. -/
theorem variance_le_of_center {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) (c : ℝ) :
    variance p f ≤ ∑ y, p y * (f y - c) ^ 2 := by
  have hexpand : ∀ y, p y * (f y - c) ^ 2
      = p y * (f y - mean p f) ^ 2 + 2 * (mean p f - c) * (p y * (f y - mean p f))
        + (mean p f - c) ^ 2 * p y := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => hexpand y, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_centered hp f, hp.total]
  have hsq : (0:ℝ) ≤ (mean p f - c) ^ 2 := sq_nonneg _
  simp only [variance, mul_zero, mul_one, add_zero]
  linarith

/-- **Popoviciu's inequality**: `Var_p(r) ≤ range(r)²/4`. -/
theorem variance_le_range_sq {p r : Ω → ℝ} (hp : IsDist p) :
    variance p r ≤ rewardRange r ^ 2 / 4 := by
  set c : ℝ := (univ.sup' univ_nonempty r + univ.inf' univ_nonempty r) / 2 with hc
  refine (variance_le_of_center hp r c).trans ?_
  have hpt : ∀ y ∈ (univ : Finset Ω), p y * (r y - c) ^ 2 ≤ p y * (rewardRange r ^ 2 / 4) := by
    intro y _
    refine mul_le_mul_of_nonneg_left ?_ (hp.nonneg y)
    have h1 : r y ≤ univ.sup' univ_nonempty r := Finset.le_sup' r (mem_univ y)
    have h2 : univ.inf' univ_nonempty r ≤ r y := Finset.inf'_le r (mem_univ y)
    simp only [rewardRange, hc]
    nlinarith [sq_nonneg (r y - c)]
  have hsum := Finset.sum_le_sum hpt
  rwa [← Finset.sum_mul, hp.total, one_mul] at hsum

/-- Every centred reward value is bounded by the reward range. -/
theorem abs_sub_mean_le_range {p r : Ω → ℝ} (hp : IsDist p) (y : Ω) :
    |r y - mean p r| ≤ rewardRange r := by
  have h1 : r y ≤ univ.sup' univ_nonempty r := Finset.le_sup' r (mem_univ y)
  have h2 : univ.inf' univ_nonempty r ≤ r y := Finset.inf'_le r (mem_univ y)
  have h3 := mean_le_sup (p := p) (r := r) hp
  have h4 := inf_le_mean (p := p) (r := r) hp
  rw [abs_le]
  simp only [rewardRange]
  constructor <;> linarith

end RLHF
-- ==== upstream: Packages/Catalog/Algebra/RLHFMeanAbsoluteDeviation.lean ====
/-!
# The sharp alignment-drift constant is the mean absolute deviation

Domain: Algebra (convex analysis × information theory × alignment theory).

Conjecture **C1** of the drift thread said that the constant in the `Θ(β⁻¹)` alignment
drift law `‖π_β − p‖₁ ≲ c/β` is the reward *standard deviation* `σ_p(r)`, refining the
earlier reward-*range* constant; the catalogue proves
`‖π_β − p‖₁ ≤ √(2 e^{range r/β} Var_p r)/β` and sandwiches an explicit family between
`σ/(2β)` and `3σ/β`.  What was left open was **the absolute constant**.

This file settles it, and the answer is *not* `σ_p(r)`.  The exact first-order drift
constant is the **mean absolute deviation**

  `MAD_p(r) = 𝔼_p |r − 𝔼_p r| ≤ σ_p(r)`,

with a *quantitative, non-asymptotic* two-sided estimate valid as soon as the
temperature exceeds the reward range:

* `RLHF.l1_drift_upper_mad` — `‖π_β − p‖₁ ≤ MAD_p(r)/β + 2 Var_p(r)/β²`;
* `RLHF.l1_drift_lower_mad` — `‖π_β − p‖₁ ≥ MAD_p(r)/β − 3 Var_p(r)/β²`;
* `RLHF.l1_drift_tendsto_mad` — hence `β·‖π_β − p‖₁ → MAD_p(r)` as `β → ∞`, so the
  constant `1` is attained by `MAD` and by no smaller functional.

The comparison with C1 is exact, via the *deviation defect identity*
`Var_p(r) − MAD_p(r)² = 𝔼_p(|r − 𝔼r| − MAD)²`:

* `RLHF.mad_le_sqrt_variance` — `MAD_p(r) ≤ σ_p(r)` always, so the σ-law of C1 is
  never violated;
* `RLHF.mad_eq_sqrt_variance_iff` — equality holds **iff** `|r − 𝔼_p r|` is constant,
  i.e. exactly for the balanced two-valued rewards.  This explains why the two-point
  family of `RLHF.variance_constant_optimal` saturated the σ-law: it is the unique
  saturating shape.
* `RLHF.mad_sq_spike_eq` — on the rare-spike family `p(true) = ε`, `r = 1_{true}`,
  `MAD² = 4ε(1−ε)·Var`, so the σ-constant is off by the unbounded factor
  `1/(2√(ε(1−ε)))`: the MAD law is *strictly*, and unboundedly, sharper.

The proof is a centred second-order expansion of the exponential tilt: writing
`u = r − 𝔼_p r`, `s = u/β` and `W = 𝔼_p e^{s}`, one has `π_β = p e^{s}/W`, `W ≥ 1` by
Jensen, `W ≤ 1 + Var/β²` by the quadratic Taylor bound `|e^x − 1 − x| ≤ x²` for
`|x| ≤ 1`, and the triangle inequality transfers `|e^{s} − W| ≈ |s|` termwise.
-/

namespace RLHF

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## 1. The deviation defect identity: `MAD ≤ σ` and its equality case -/

/-- **Deviation defect identity.**  `Var_p(f) − MAD_p(f)² = 𝔼_p(|f − 𝔼_p f| − MAD_p f)²`:
the gap between the variance and the squared mean absolute deviation is itself the
variance of the absolute deviation. -/
theorem variance_sub_mad_sq {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) :
    variance p f - mad p f ^ 2 = ∑ y, p y * (|f y - mean p f| - mad p f) ^ 2 := by
  have hexp : ∀ y, p y * (|f y - mean p f| - mad p f) ^ 2
      = p y * (f y - mean p f) ^ 2 - 2 * mad p f * (p y * |f y - mean p f|)
        + mad p f ^ 2 * p y := by
    intro y
    have habs : |f y - mean p f| ^ 2 = (f y - mean p f) ^ 2 := sq_abs _
    have hring : (|f y - mean p f| - mad p f) ^ 2
        = |f y - mean p f| ^ 2 - 2 * mad p f * |f y - mean p f| + mad p f ^ 2 := by ring
    rw [hring, habs]
    ring
  rw [Finset.sum_congr rfl fun y _ => hexp y, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hp.total]
  simp only [variance, mad]
  ring

/-- `MAD_p(f)² ≤ Var_p(f)`. -/
theorem mad_sq_le_variance {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) :
    mad p f ^ 2 ≤ variance p f := by
  have h := variance_sub_mad_sq hp f
  have hnn : 0 ≤ ∑ y, p y * (|f y - mean p f| - mad p f) ^ 2 :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hp.nonneg y) (sq_nonneg _)
  linarith

/-- **The mean absolute deviation never exceeds the standard deviation.**  Hence the
sharp `MAD/β` drift law of this file is never weaker than the `σ/β` law of C1. -/
theorem mad_le_sqrt_variance {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) :
    mad p f ≤ Real.sqrt (variance p f) := by
  have h := mad_sq_le_variance hp f
  have hs := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (mad_nonneg hp f)] at hs

/-- **Equality case.**  `MAD_p(f) = σ_p(f)` exactly when the absolute deviation
`|f − 𝔼_p f|` is constant on the support — i.e. for the balanced two-valued rewards. -/
theorem mad_eq_sqrt_variance_iff {p : Ω → ℝ} (hp : IsPosDist p) (f : Ω → ℝ) :
    mad p f = Real.sqrt (variance p f) ↔ ∀ y, |f y - mean p f| = mad p f := by
  have hd := hp.isDist
  constructor
  · intro h
    have hsq : mad p f ^ 2 = variance p f := by
      rw [h, Real.sq_sqrt (variance_nonneg hd f)]
    have hzero : ∑ y, p y * (|f y - mean p f| - mad p f) ^ 2 = 0 := by
      rw [← variance_sub_mad_sq hd f, hsq]; ring
    intro y
    have hle : p y * (|f y - mean p f| - mad p f) ^ 2
        ≤ ∑ z, p z * (|f z - mean p f| - mad p f) ^ 2 :=
      Finset.single_le_sum (f := fun z => p z * (|f z - mean p f| - mad p f) ^ 2)
        (fun z _ => mul_nonneg (hp.pos z).le (sq_nonneg _)) (mem_univ y)
    rw [hzero] at hle
    have hterm : p y * (|f y - mean p f| - mad p f) ^ 2 = 0 :=
      le_antisymm hle (mul_nonneg (hp.pos y).le (sq_nonneg _))
    rcases mul_eq_zero.1 hterm with h1 | h2
    · exact absurd h1 (ne_of_gt (hp.pos y))
    · have hz : |f y - mean p f| - mad p f = 0 := by
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
      linarith
  · intro h
    have hsq : mad p f ^ 2 = variance p f := by
      have hzero : ∑ y, p y * (|f y - mean p f| - mad p f) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [h y]; ring
      have hid := variance_sub_mad_sq hd f
      rw [hzero] at hid
      linarith
    rw [← hsq, Real.sqrt_sq (mad_nonneg hd f)]

variable [Nonempty Ω]

/-- The mean absolute deviation is bounded by the reward range. -/
theorem mad_le_range {p r : Ω → ℝ} (hp : IsDist p) : mad p r ≤ rewardRange r := by
  have h : ∀ y ∈ (univ : Finset Ω), p y * |r y - mean p r| ≤ p y * rewardRange r :=
    fun y _ => mul_le_mul_of_nonneg_left (abs_sub_mean_le_range hp y) (hp.nonneg y)
  have hs := Finset.sum_le_sum h
  rwa [← Finset.sum_mul, hp.total, one_mul] at hs

/-! ## 2. The centred tilt normaliser -/

/-- The **centred partition function** `W_β = 𝔼_p e^{(r − 𝔼_p r)/β}`.  It is the
partition function of the reward shifted to have zero mean, and satisfies `W_β ≥ 1`. -/
-- [dropped: platform already declares tiltNorm]
theorem tiltNorm_pos {β : ℝ} {r p : Ω → ℝ} (hp : IsPosDist p) : 0 < tiltNorm β r p :=
  Finset.sum_pos (fun y _ => mul_pos (hp.pos y) (Real.exp_pos _)) univ_nonempty

omit [Nonempty Ω] in
/-- **Jensen.**  The centred partition function is at least `1`. -/
theorem one_le_tiltNorm {β : ℝ} {r p : Ω → ℝ} (hp : IsDist p) : 1 ≤ tiltNorm β r p := by
  have hle : ∀ y ∈ (univ : Finset Ω), p y * (1 + (r y - mean p r) / β)
      ≤ p y * Real.exp ((r y - mean p r) / β) := by
    intro y _
    refine mul_le_mul_of_nonneg_left ?_ (hp.nonneg y)
    linarith [Real.add_one_le_exp ((r y - mean p r) / β)]
  have hsum := Finset.sum_le_sum hle
  have hlin : ∑ y, p y * (1 + (r y - mean p r) / β) = 1 := by
    have h : ∀ y, p y * (1 + (r y - mean p r) / β)
        = p y + (1 / β) * (p y * (r y - mean p r)) := fun y => by ring
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_centered hp r, hp.total]
    ring
  rw [hlin] at hsum
  exact hsum

/-- The quadratic Taylor control of the centred partition function:
`W_β ≤ 1 + Var_p(r)/β²` whenever the temperature exceeds the reward range. -/
theorem tiltNorm_le {β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsDist p)
    (hr : rewardRange r ≤ β) :
    tiltNorm β r p ≤ 1 + variance p r / β ^ 2 := by
  have hsmall : ∀ y, |(r y - mean p r) / β| ≤ 1 := by
    intro y
    rw [abs_div, abs_of_pos hβ, div_le_one hβ]
    exact le_trans (abs_sub_mean_le_range hp y) hr
  have hle : ∀ y ∈ (univ : Finset Ω), p y * Real.exp ((r y - mean p r) / β)
      ≤ p y * (1 + (r y - mean p r) / β + ((r y - mean p r) / β) ^ 2) := by
    intro y _
    refine mul_le_mul_of_nonneg_left ?_ (hp.nonneg y)
    have htaylor := abs_le.1 (Real.abs_exp_sub_one_sub_id_le (hsmall y))
    linarith [htaylor.2]
  have hsum := Finset.sum_le_sum hle
  have hrhs : ∑ y, p y * (1 + (r y - mean p r) / β + ((r y - mean p r) / β) ^ 2)
      = 1 + variance p r / β ^ 2 := by
    have h : ∀ y, p y * (1 + (r y - mean p r) / β + ((r y - mean p r) / β) ^ 2)
        = p y + (1 / β) * (p y * (r y - mean p r))
          + (1 / β ^ 2) * (p y * (r y - mean p r) ^ 2) := by
      intro y; ring
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_centered hp r, hp.total]
    simp only [variance]
    ring
  rw [hrhs] at hsum
  exact hsum

/-! ## 3. The Gibbs policy in centred form -/

omit [Nonempty Ω] in
theorem partition_eq_tiltNorm {β : ℝ} {r p : Ω → ℝ} :
    partition β r p = Real.exp (mean p r / β) * tiltNorm β r p := by
  rw [partition, tiltNorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← mul_assoc, mul_comm (Real.exp (mean p r / β)) (p y), mul_assoc, ← Real.exp_add,
    show mean p r / β + (r y - mean p r) / β = r y / β by ring]

omit [Nonempty Ω] in
theorem gibbsPolicy_eq_centred {β : ℝ} {r p : Ω → ℝ} (y : Ω) :
    gibbsPolicy β r p y = p y * Real.exp ((r y - mean p r) / β) / tiltNorm β r p := by
  have hexp : Real.exp (r y / β)
      = Real.exp (mean p r / β) * Real.exp ((r y - mean p r) / β) := by
    rw [← Real.exp_add, show mean p r / β + (r y - mean p r) / β = r y / β by ring]
  have h0 : Real.exp (mean p r / β) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [gibbsPolicy, partition_eq_tiltNorm, hexp,
    show p y * (Real.exp (mean p r / β) * Real.exp ((r y - mean p r) / β))
      = Real.exp (mean p r / β) * (p y * Real.exp ((r y - mean p r) / β)) by ring,
    mul_div_mul_left _ _ h0]

/-- The `ℓ¹` drift in centred form: `‖π_β − p‖₁ = 𝔼_p|e^{s} − W| / W`. -/
theorem l1Dist_gibbs_eq {β : ℝ} {r p : Ω → ℝ} (hp : IsPosDist p) :
    l1Dist (gibbsPolicy β r p) p
      = (∑ y, p y * |Real.exp ((r y - mean p r) / β) - tiltNorm β r p|) / tiltNorm β r p := by
  have hW := tiltNorm_pos (β := β) (r := r) hp
  rw [l1Dist, Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [gibbsPolicy_eq_centred]
  have hsub : p y * Real.exp ((r y - mean p r) / β) / tiltNorm β r p - p y
      = (p y * (Real.exp ((r y - mean p r) / β) - tiltNorm β r p)) / tiltNorm β r p := by
    field_simp
  rw [hsub, abs_div, abs_of_pos hW, abs_mul, abs_of_pos (hp.pos y)]

/-! ## 4. The sharp two-sided drift law -/

/-- The centred `ℓ¹` numerator `S_β = 𝔼_p|e^{(r−𝔼r)/β} − W_β|` is within `2 Var/β²` of
`MAD_p(r)/β`.  This is the analytic heart of the sharp drift law. -/
theorem abs_l1_numerator_sub_mad {β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsDist p)
    (hr : rewardRange r ≤ β) :
    abs ((∑ y, p y * |Real.exp ((r y - mean p r) / β) - tiltNorm β r p|) - mad p r / β)
      ≤ 2 * (variance p r / β ^ 2) := by
  have hsmall : ∀ y, |(r y - mean p r) / β| ≤ 1 := by
    intro y
    rw [abs_div, abs_of_pos hβ, div_le_one hβ]
    exact le_trans (abs_sub_mean_le_range hp y) hr
  have hW1 := one_le_tiltNorm (β := β) (r := r) hp
  have hW2 := tiltNorm_le (β := β) (r := r) hβ hp hr
  have hmadeq : mad p r / β = ∑ y, p y * |(r y - mean p r) / β| := by
    rw [mad, Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [abs_div, abs_of_pos hβ]
    ring
  rw [hmadeq, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ y ∈ (univ : Finset Ω),
      abs (p y * |Real.exp ((r y - mean p r) / β) - tiltNorm β r p|
        - p y * |(r y - mean p r) / β|)
      ≤ p y * (((r y - mean p r) / β) ^ 2 + variance p r / β ^ 2) := by
    intro y _
    set s := (r y - mean p r) / β with hs
    have htri : abs (|Real.exp s - tiltNorm β r p| - |s|)
        ≤ |Real.exp s - tiltNorm β r p - s| := abs_abs_sub_abs_le_abs_sub _ _
    have hsplit : |Real.exp s - tiltNorm β r p - s|
        ≤ |Real.exp s - 1 - s| + |tiltNorm β r p - 1| := by
      rw [show Real.exp s - tiltNorm β r p - s
          = (Real.exp s - 1 - s) - (tiltNorm β r p - 1) by ring]
      exact abs_sub _ _
    have h1 : |Real.exp s - 1 - s| ≤ s ^ 2 := Real.abs_exp_sub_one_sub_id_le (hsmall y)
    have h2 : |tiltNorm β r p - 1| ≤ variance p r / β ^ 2 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hcomb : abs (|Real.exp s - tiltNorm β r p| - |s|)
        ≤ s ^ 2 + variance p r / β ^ 2 := by linarith
    calc abs (p y * |Real.exp s - tiltNorm β r p| - p y * |s|)
        = p y * abs (|Real.exp s - tiltNorm β r p| - |s|) := by
          rw [← mul_sub, abs_mul, abs_of_nonneg (hp.nonneg y)]
      _ ≤ p y * (s ^ 2 + variance p r / β ^ 2) :=
          mul_le_mul_of_nonneg_left hcomb (hp.nonneg y)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hrhs : ∑ y, p y * (((r y - mean p r) / β) ^ 2 + variance p r / β ^ 2)
      = variance p r / β ^ 2 + variance p r / β ^ 2 := by
    have h : ∀ y, p y * (((r y - mean p r) / β) ^ 2 + variance p r / β ^ 2)
        = (1 / β ^ 2) * (p y * (r y - mean p r) ^ 2) + (variance p r / β ^ 2) * p y := by
      intro y; ring
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hp.total]
    simp only [variance]
    ring
  rw [hrhs]
  linarith

/-- **Sharp drift upper bound.**  For any temperature above the reward range,
`‖π_β − p‖₁ ≤ MAD_p(r)/β + 2 Var_p(r)/β²`.  The leading constant is `1`, and the
functional is the mean absolute deviation, not the standard deviation. -/
theorem l1_drift_upper_mad {β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hr : rewardRange r ≤ β) :
    l1Dist (gibbsPolicy β r p) p ≤ mad p r / β + 2 * (variance p r / β ^ 2) := by
  have hd := hp.isDist
  have hW1 := one_le_tiltNorm (β := β) (r := r) hd
  have hnum := abs_l1_numerator_sub_mad hβ hd hr
  set S := ∑ y, p y * |Real.exp ((r y - mean p r) / β) - tiltNorm β r p| with hS
  have hSnn : 0 ≤ S :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hp.pos y).le (abs_nonneg _)
  have hSle : S ≤ mad p r / β + 2 * (variance p r / β ^ 2) := by
    have h := (abs_le.1 hnum).2
    linarith
  rw [l1Dist_gibbs_eq hp, ← hS]
  exact le_trans (div_le_self hSnn hW1) hSle

/-- **Sharp drift lower bound.**  For any temperature above the reward range,
`‖π_β − p‖₁ ≥ MAD_p(r)/β − 3 Var_p(r)/β²`.  Together with `l1_drift_upper_mad` this
pins the drift to `MAD_p(r)/β` up to `O(β⁻²)`. -/
theorem l1_drift_lower_mad {β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hr : rewardRange r ≤ β) :
    mad p r / β - 3 * (variance p r / β ^ 2) ≤ l1Dist (gibbsPolicy β r p) p := by
  have hd := hp.isDist
  have hW1 := one_le_tiltNorm (β := β) (r := r) hd
  have hW2 := tiltNorm_le (β := β) (r := r) hβ hd hr
  have hW := tiltNorm_pos (β := β) (r := r) hp
  have hV : 0 ≤ variance p r := variance_nonneg hd r
  have hVb : 0 ≤ variance p r / β ^ 2 := by positivity
  have hnum := abs_l1_numerator_sub_mad hβ hd hr
  set S := ∑ y, p y * |Real.exp ((r y - mean p r) / β) - tiltNorm β r p| with hS
  have hSnn : 0 ≤ S :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hp.pos y).le (abs_nonneg _)
  have hSge : mad p r / β - 2 * (variance p r / β ^ 2) ≤ S := by
    have h := (abs_le.1 hnum).1
    linarith
  have hmadb : mad p r / β ≤ 1 := by
    rw [div_le_one hβ]
    exact le_trans (mad_le_range (r := r) hd) hr
  rw [l1Dist_gibbs_eq hp, ← hS]
  rcases le_or_gt (mad p r / β - 2 * (variance p r / β ^ 2)) 0 with hneg | hpos
  · have hnn : 0 ≤ S / tiltNorm β r p := div_nonneg hSnn hW.le
    linarith
  · -- `S / W ≥ X / W ≥ X − X (W − 1) ≥ MAD/β − 2V/β² − V/β²`
    set X := mad p r / β - 2 * (variance p r / β ^ 2) with hX
    have hstep : X / tiltNorm β r p ≤ S / tiltNorm β r p :=
      (div_le_div_iff_of_pos_right hW).mpr hSge
    have hkey : X - X * (tiltNorm β r p - 1) ≤ X / tiltNorm β r p := by
      rw [le_div_iff₀ hW]
      nlinarith [sq_nonneg (tiltNorm β r p - 1), hpos.le]
    have hXle : X ≤ 1 := by
      have h2 : 0 ≤ 2 * (variance p r / β ^ 2) := by positivity
      linarith
    have hprod : X * (tiltNorm β r p - 1) ≤ variance p r / β ^ 2 := by
      nlinarith [hpos.le]
    linarith

/-- **The alignment-drift constant is exactly the mean absolute deviation.**
`β · ‖π_β − p‖₁ → MAD_p(r)` as the KL temperature `β → ∞`.  This determines the
absolute constant left open by C1: it is `1` for `MAD_p(r)`, hence `MAD/σ ≤ 1` for the
standard deviation. -/
theorem l1_drift_tendsto_mad {r p : Ω → ℝ} (hp : IsPosDist p) :
    Filter.Tendsto (fun β : ℝ => β * l1Dist (gibbsPolicy β r p) p) Filter.atTop
      (nhds (mad p r)) := by
  have hlow : Filter.Tendsto (fun β : ℝ => mad p r - 3 * (variance p r / β)) Filter.atTop
      (nhds (mad p r)) := by
    have h0 : Filter.Tendsto (fun β : ℝ => variance p r / β) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
    have h : Filter.Tendsto (fun β : ℝ => 3 * (variance p r / β)) Filter.atTop (nhds 0) := by
      simpa using h0.const_mul (3 : ℝ)
    simpa using tendsto_const_nhds.sub h
  have hhigh : Filter.Tendsto (fun β : ℝ => mad p r + 2 * (variance p r / β)) Filter.atTop
      (nhds (mad p r)) := by
    have h0 : Filter.Tendsto (fun β : ℝ => variance p r / β) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
    have h : Filter.Tendsto (fun β : ℝ => 2 * (variance p r / β)) Filter.atTop (nhds 0) := by
      simpa using h0.const_mul (2 : ℝ)
    simpa using tendsto_const_nhds.add h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (max (rewardRange r) 1)] with β hβm
    have hβ : 0 < β := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hβm)
    have hr : rewardRange r ≤ β := le_trans (le_max_left _ _) hβm
    have h := mul_le_mul_of_nonneg_left (l1_drift_lower_mad hβ hp hr) hβ.le
    calc mad p r - 3 * (variance p r / β)
        = β * (mad p r / β - 3 * (variance p r / β ^ 2)) := by field_simp
      _ ≤ β * l1Dist (gibbsPolicy β r p) p := h
  · filter_upwards [Filter.eventually_ge_atTop (max (rewardRange r) 1)] with β hβm
    have hβ : 0 < β := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hβm)
    have hr : rewardRange r ≤ β := le_trans (le_max_left _ _) hβm
    have h := mul_le_mul_of_nonneg_left (l1_drift_upper_mad hβ hp hr) hβ.le
    calc β * l1Dist (gibbsPolicy β r p) p
        ≤ β * (mad p r / β + 2 * (variance p r / β ^ 2)) := h
      _ = mad p r + 2 * (variance p r / β) := by field_simp

/-! ## 5. Separation from the standard-deviation law: the rare-spike family -/

/-- The Bernoulli reference policy `p(true) = e`. -/
-- [dropped: platform already declares bern]
-- [dropped: platform already declares spike]
theorem bern_isPosDist {e : ℝ} (h0 : 0 < e) (h1 : e < 1) : IsPosDist (bern e) where
  pos := by intro b; cases b <;> simp [bern] <;> linarith
  total := by simp [bern]

theorem mean_bern_spike (e : ℝ) : mean (bern e) spike = e := by
  simp [mean, bern, spike]

theorem mad_bern_spike {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    mad (bern e) spike = 2 * e * (1 - e) := by
  rw [mad, mean_bern_spike]
  simp only [bern, spike, Fintype.sum_bool, cond_true, cond_false]
  rw [show |(0:ℝ) - e| = e from by rw [zero_sub, abs_neg, abs_of_nonneg h0],
    show |(1:ℝ) - e| = 1 - e from abs_of_nonneg (by linarith)]
  ring

theorem variance_bern_spike (e : ℝ) : variance (bern e) spike = e * (1 - e) := by
  rw [variance, mean_bern_spike]
  simp only [bern, spike, Fintype.sum_bool, cond_true, cond_false]
  ring

/-- **The standard-deviation constant is unboundedly lossy.**  On the rare-spike family
`p(true) = ε`, `r = 1_{true}` one has `MAD² = 4ε(1−ε)·Var`, i.e.
`MAD/σ = 2√(ε(1−ε)) → 0` as `ε → 0`: the sharp `MAD/β` law beats the `σ/β` law of C1 by
an arbitrarily large factor. -/
theorem mad_sq_spike_eq {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    mad (bern e) spike ^ 2 = 4 * e * (1 - e) * variance (bern e) spike := by
  rw [mad_bern_spike h0 h1, variance_bern_spike]
  ring

/-- The saturating case of `mad_eq_sqrt_variance_iff`: the balanced two-point reward,
where `MAD = σ` and the σ-law of C1 is exactly the sharp law. -/
theorem mad_eq_sqrt_variance_balanced :
    mad (bern (1/2)) spike = Real.sqrt (variance (bern (1/2)) spike) := by
  rw [mad_bern_spike (by norm_num) (by norm_num), variance_bern_spike,
    show (1:ℝ)/2 * (1 - 1/2) = (1/2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

end RLHF
section
open RLHF
open Finset
variable {Ω : Type*} [Fintype Ω]
variable [Nonempty Ω]

theorem solution {β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hr : rewardRange r ≤ β) :
    mad p r / β - 3 * (variance p r / β ^ 2) ≤ l1Dist (gibbsPolicy β r p) p := by
  first
  | exact RLHF.l1_drift_lower_mad hβ hp hr
  | exact RLHF.l1_drift_lower_mad
  | exact @RLHF.l1_drift_lower_mad _ r p hβ hp hr
  | apply RLHF.l1_drift_lower_mad
  | exact RLHF.l1_drift_lower_mad ..


end
