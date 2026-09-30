-- Prove2me | solution 1 for MarkovChainCLT.abs_covariance_le_two_mul_sqrt_phiMixingCoef
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:06:19.014921+00:00
-- url     : https://prove2.me/submissions/6a2320a8-d610-4897-9ac1-fbc4b170984d

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_MarkovChainCLT_indicator_cov_le_phi
import Mathlib.Probability.Moments.Variance

open scoped BigOperators

namespace FiniteSchur

variable {I J : Type*} [Fintype I] [Fintype J]

theorem sum_abs_le_two_mul (d : I → ℝ) (c : ℝ)
    (hsum : ∑ i, d i = 0) (hset : ∀ s : Finset I, ∑ i ∈ s, d i ≤ c) :
    ∑ i, |d i| ≤ 2 * c := by
  classical
  have hpoint (i : I) : |d i| = 2 * (if 0 ≤ d i then d i else 0) - d i := by
    split_ifs with hi
    · rw [abs_of_nonneg hi]
      ring
    · rw [abs_of_neg (lt_of_not_ge hi)]
      ring
  calc
    _ = ∑ i, (2 * (if 0 ≤ d i then d i else 0) - d i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hpoint i
    _ = 2 * ∑ i ∈ Finset.univ.filter (fun i => 0 ≤ d i), d i := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, sub_zero,
        Finset.sum_filter]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hset _) (by norm_num)

theorem bilinear_sq_le (d : I → J → ℝ) (p : I → ℝ) (r : J → ℝ)
    (A B : ℝ)
    (hrow : ∀ i, ∑ j, |d i j| ≤ A * p i)
    (hcol : ∀ j, ∑ i, |d i j| ≤ B * r j) (u : I → ℝ) (v : J → ℝ) :
    (∑ i, ∑ j, u i * v j * d i j) ^ 2 ≤
      A * B * (∑ i, p i * (u i) ^ 2) * (∑ j, r j * (v j) ^ 2) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (R := ℝ) (Finset.univ : Finset (I × J))
    (r := fun ij => u ij.1 * v ij.2 * d ij.1 ij.2)
    (f := fun ij => |d ij.1 ij.2| * (u ij.1) ^ 2)
    (g := fun ij => |d ij.1 ij.2| * (v ij.2) ^ 2)
    (fun ij _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun ij _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun ij _ => by
      rw [mul_pow, mul_pow, ← sq_abs (d ij.1 ij.2)]
      ring_nf
      exact le_rfl)
  simp only [Fintype.sum_prod_type] at hcs
  have hleft : (∑ i, ∑ j, |d i j| * (u i) ^ 2) ≤
      A * ∑ i, p i * (u i) ^ 2 := by
    calc
      _ = ∑ i, (∑ j, |d i j|) * (u i) ^ 2 := by simp_rw [Finset.sum_mul]
      _ ≤ ∑ i, (A * p i) * (u i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
      _ = _ := by simp_rw [mul_assoc, Finset.mul_sum]
  have hright : (∑ i, ∑ j, |d i j| * (v j) ^ 2) ≤
      B * ∑ j, r j * (v j) ^ 2 := by
    calc
      _ = ∑ j, (∑ i, |d i j|) * (v j) ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
      _ ≤ ∑ j, (B * r j) * (v j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
      _ = _ := by simp_rw [mul_assoc, Finset.mul_sum]
  calc
    _ ≤ _ := hcs
    _ ≤ (A * ∑ i, p i * (u i) ^ 2) * (B * ∑ j, r j * (v j) ^ 2) :=
      mul_le_mul hleft hright
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (abs_nonneg _) (sq_nonneg _))
        ((Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (abs_nonneg _) (sq_nonneg _)).trans hleft)
    _ = _ := by ring

theorem abs_bilinear_le (d : I → J → ℝ) (p : I → ℝ) (r : J → ℝ)
    (phi : ℝ) (hphi : 0 ≤ phi)
    (hp : ∀ i, 0 ≤ p i) (hr : ∀ j, 0 ≤ r j)
    (hrow : ∀ i, ∑ j, |d i j| ≤ 2 * phi * p i)
    (hcol : ∀ j, ∑ i, |d i j| ≤ 2 * r j) (u : I → ℝ) (v : J → ℝ) :
    |∑ i, ∑ j, u i * v j * d i j| ≤
      2 * Real.sqrt phi * Real.sqrt (∑ i, p i * (u i) ^ 2) *
        Real.sqrt (∑ j, r j * (v j) ^ 2) := by
  have hsq := bilinear_sq_le d p r (2 * phi) 2 hrow hcol u v
  have hu : 0 ≤ ∑ i, p i * (u i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)
  have hv : 0 ≤ ∑ j, r j * (v j) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hr j) (sq_nonneg _)
  have hrhs : 0 ≤ 2 * Real.sqrt phi * Real.sqrt (∑ i, p i * (u i) ^ 2) *
      Real.sqrt (∑ j, r j * (v j) ^ 2) := by positivity
  apply abs_le_of_sq_le_sq ?_ hrhs
  calc
    _ ≤ _ := hsq
    _ = _ := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hphi, Real.sq_sqrt hu,
        Real.sq_sqrt hv]
      ring

end FiniteSchur

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators ProbabilityTheory

local infixr:25 " →ₛ " => MeasureTheory.SimpleFunc

namespace SimpleCovariance

variable {Ω : Type*} [MeasurableSpace Ω]

theorem sum_fiber_real (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω →ₛ ℝ)
    (s : Finset ℝ) :
    (∑ x ∈ s, μ.real (f ⁻¹' {x})) = μ.real (f ⁻¹' (s : Set ℝ)) := by
  have h := congrArg ENNReal.toReal (f.sum_measure_preimage_singleton (μ := μ) s)
  rw [ENNReal.toReal_sum (fun x _ => measure_ne_top μ _)] at h
  exact h

theorem sum_inter_fiber_real (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω →ₛ ℝ)
    (s : Set Ω) (t : Finset ℝ) :
    (∑ x ∈ t, μ.real (s ∩ f ⁻¹' {x})) = μ.real (s ∩ f ⁻¹' (t : Set ℝ)) := by
  simpa only [measureReal_restrict_apply (f.measurableSet_preimage _), Set.inter_comm]
    using sum_fiber_real (μ.restrict s) f t

theorem sum_range_inter_fiber_real (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω →ₛ ℝ)
    (s : Set Ω) :
    (∑ x ∈ f.range, μ.real (s ∩ f ⁻¹' {x})) = μ.real s := by
  rw [sum_inter_fiber_real]
  simp only [SimpleFunc.coe_range, Set.preimage_range, Set.inter_univ]

theorem integral_sq_eq_sum (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω →ₛ ℝ) :
    (∫ ω, (f ω) ^ 2 ∂μ) = ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * x ^ 2 := by
  have h := f.map_integral (μ := μ) (fun x => x ^ 2)
    (f.integrable_of_isFiniteMeasure) (by simp)
  rw [(f.map (fun x => x ^ 2)).integral_eq_integral
    (f.map (fun x => x ^ 2)).integrable_of_isFiniteMeasure] at h
  simpa only [SimpleFunc.map_apply, smul_eq_mul] using h

theorem integral_mul_eq_sum (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω →ₛ ℝ) :
    (∫ ω, f ω * g ω ∂μ) =
      ∑ x ∈ f.range, ∑ y ∈ g.range,
        x * y * μ.real (f ⁻¹' {x} ∩ g ⁻¹' {y}) := by
  classical
  have hpoint (ω : Ω) : f ω * g ω =
      ∑ x ∈ f.range, (f ⁻¹' {x}).indicator (fun ω => x * g ω) ω := by
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
    rw [Finset.sum_eq_single (f ω)]
    · simp
    · intro x hx hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot (f.mem_range_self ω)).elim
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [integral_indicator (f.measurableSet_fiber x), integral_const_mul,
      g.integral_eq_sum g.integrable_of_isFiniteMeasure, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [measureReal_restrict_apply (g.measurableSet_fiber y)]
    simp only [smul_eq_mul, Set.inter_comm]
    ring
  · intro x hx
    exact (g.integrable_of_isFiniteMeasure.const_mul x).indicator (f.measurableSet_fiber x)

theorem sum_abs_finset_le_two_mul (s : Finset ℝ) (d : ℝ → ℝ) (c : ℝ)
    (hsum : ∑ i ∈ s, d i = 0) (hset : ∀ t : Finset ℝ, ∑ i ∈ t, d i ≤ c) :
    ∑ i ∈ s, |d i| ≤ 2 * c := by
  classical
  have hpoint (i : ℝ) : |d i| = 2 * (if 0 ≤ d i then d i else 0) - d i := by
    split_ifs with hi
    · rw [abs_of_nonneg hi]
      ring
    · rw [abs_of_neg (lt_of_not_ge hi)]
      ring
  calc
    _ = ∑ i ∈ s, (2 * (if 0 ≤ d i then d i else 0) - d i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hpoint i
    _ = 2 * ∑ i ∈ s.filter (fun i => 0 ≤ d i), d i := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, sub_zero,
        Finset.sum_filter]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hset _) (by norm_num)

theorem abs_covariance_le (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω →ₛ ℝ)
    (phi : ℝ) (hphi : 0 ≤ phi)
    (hmix : ∀ S T : Set ℝ,
      |μ.real (f ⁻¹' S ∩ g ⁻¹' T) - μ.real (f ⁻¹' S) * μ.real (g ⁻¹' T)| ≤
        phi * μ.real (f ⁻¹' S)) :
    |cov[f, g; μ]| ≤ 2 * Real.sqrt phi *
      (Real.sqrt (∫ ω, (f ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (g ω) ^ 2 ∂μ)) := by
  classical
  let p (x : ℝ) := μ.real (f ⁻¹' {x})
  let r (y : ℝ) := μ.real (g ⁻¹' {y})
  let q (x y : ℝ) := μ.real (f ⁻¹' {x} ∩ g ⁻¹' {y})
  let d (x y : ℝ) := q x y - p x * r y
  have hp (x : ℝ) : 0 ≤ p x := measureReal_nonneg
  have hr (y : ℝ) : 0 ≤ r y := measureReal_nonneg
  have hq (x y : ℝ) : 0 ≤ q x y := measureReal_nonneg
  have hpone : ∑ x ∈ f.range, p x = 1 := by
    dsimp [p]
    rw [sum_fiber_real]
    simp
  have hrone : ∑ y ∈ g.range, r y = 1 := by
    dsimp [r]
    rw [sum_fiber_real]
    simp
  have hqrow (x : ℝ) : ∑ y ∈ g.range, q x y = p x :=
    sum_range_inter_fiber_real μ g (f ⁻¹' {x})
  have hqcol (y : ℝ) : ∑ x ∈ f.range, q x y = r y := by
    simpa only [q, r, Set.inter_comm] using
      sum_range_inter_fiber_real μ f (g ⁻¹' {y})
  have hrow (x : ℝ) : ∑ y ∈ g.range, |d x y| ≤ 2 * phi * p x := by
    have hsum : ∑ y ∈ g.range, d x y = 0 := by
      simp only [d, Finset.sum_sub_distrib, ← Finset.mul_sum, hqrow, hrone,
        mul_one, sub_self]
    have hset (t : Finset ℝ) : ∑ y ∈ t, d x y ≤ phi * p x := by
      dsimp [d, q, p, r]
      rw [Finset.sum_sub_distrib, sum_inter_fiber_real, ← Finset.mul_sum,
        sum_fiber_real]
      exact (le_abs_self _).trans (hmix {x} (t : Set ℝ))
    simpa only [mul_assoc] using sum_abs_finset_le_two_mul g.range (d x) (phi * p x) hsum hset
  have hcol (y : ℝ) : ∑ x ∈ f.range, |d x y| ≤ 2 * r y := by
    calc
      _ ≤ ∑ x ∈ f.range, (q x y + p x * r y) := by
        apply Finset.sum_le_sum
        intro x hx
        apply abs_le.2
        have hn := mul_nonneg (hp x) (hr y)
        dsimp [d]
        constructor <;> linarith [hq x y]
      _ = _ := by rw [Finset.sum_add_distrib, hqcol, ← Finset.sum_mul, hpone]; ring
  have hschur : |∑ x ∈ f.range, ∑ y ∈ g.range, x * y * d x y| ≤
      2 * Real.sqrt phi * Real.sqrt (∑ x ∈ f.range, p x * x ^ 2) *
        Real.sqrt (∑ y ∈ g.range, r y * y ^ 2) := by
    have hs := FiniteSchur.abs_bilinear_le
        (fun (x : ↥f.range) (y : ↥g.range) => d x y)
        (fun x : ↥f.range => p x) (fun y : ↥g.range => r y) phi hphi
        (fun x => hp x) (fun y => hr y)
        (fun x => by
          rw [Finset.sum_coe_sort g.range (fun y => |d x y|)]
          exact hrow x)
        (fun y => by
          rw [Finset.sum_coe_sort f.range (fun x => |d x y|)]
          exact hcol y)
        (fun x => (x : ℝ)) (fun y => (y : ℝ))
    have hsum : (∑ x : ↥f.range, ∑ y : ↥g.range, (x : ℝ) * (y : ℝ) * d x y) =
        ∑ x ∈ f.range, ∑ y ∈ g.range, x * y * d x y := by
      rw [Finset.sum_coe_sort f.range (fun x => ∑ y : ↥g.range, x * (y : ℝ) * d x y)]
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_coe_sort g.range (fun y => x * y * d x y)
    rw [hsum, Finset.sum_coe_sort f.range (fun x => p x * x ^ 2),
      Finset.sum_coe_sort g.range (fun y => r y * y ^ 2)] at hs
    exact hs
  have hcov : cov[f, g; μ] = ∑ x ∈ f.range, ∑ y ∈ g.range, x * y * d x y := by
    rw [covariance_eq_sub (f.memLp_of_isFiniteMeasure 2 μ) (g.memLp_of_isFiniteMeasure 2 μ)]
    change (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ) = _
    rw [integral_mul_eq_sum, f.integral_eq_sum f.integrable_of_isFiniteMeasure,
      g.integral_eq_sum g.integrable_of_isFiniteMeasure]
    simp only [smul_eq_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [d, p, r, q]
    ring
  rw [← hcov] at hschur
  have hf2 : (∑ x ∈ f.range, p x * x ^ 2) = ∫ ω, (f ω) ^ 2 ∂μ :=
    (integral_sq_eq_sum μ f).symm
  have hg2 : (∑ y ∈ g.range, r y * y ^ 2) = ∫ ω, (g ω) ^ 2 ∂μ :=
    (integral_sq_eq_sum μ g).symm
  simpa only [hf2, hg2, mul_assoc] using hschur

end SimpleCovariance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology

namespace SimpleApproximation

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def approx (f : Ω → ℝ) (hf : Measurable f) (n : ℕ) : SimpleFunc Ω ℝ :=
  SimpleFunc.approxOn f hf Set.univ 0 (Set.mem_univ _) n

theorem approx_comp (f : Ω → ℝ) (hf : Measurable f) (n : ℕ) :
    approx f hf n = (approx (id : ℝ → ℝ) measurable_id n).comp f hf := rfl

theorem norm_approx_le (f : Ω → ℝ) (hf : Measurable f) (n : ℕ) (x : Ω) :
    ‖approx f hf n x‖ ≤ 2 * ‖f x‖ := by
  simpa only [two_mul] using
    SimpleFunc.norm_approxOn_zero_le hf (Set.mem_univ (0 : ℝ)) x n

theorem tendsto_approx (f : Ω → ℝ) (hf : Measurable f) (x : Ω) :
    Tendsto (fun n => approx f hf n x) atTop (𝓝 (f x)) := by
  exact SimpleFunc.tendsto_approxOn hf (Set.mem_univ (0 : ℝ)) (by simp)

theorem memLp_approx (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 μ) (n : ℕ) :
    MemLp (approx f hf n) 2 μ :=
  SimpleFunc.memLp_approxOn hf hf2 (Set.mem_univ (0 : ℝ)) (memLp_const 0) n

theorem tendsto_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 μ) :
    Tendsto (fun n => ∫ x, approx f hf n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => 2 * ‖f x‖)
  · intro n
    exact (approx f hf n).aestronglyMeasurable
  · exact (hf2.integrable one_le_two).norm.const_mul 2
  · intro n
    exact Filter.Eventually.of_forall (norm_approx_le f hf n)
  · exact Filter.Eventually.of_forall (tendsto_approx f hf)

theorem tendsto_integral_mul (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) :
    Tendsto (fun n => ∫ x, approx f hf n x * approx g hg n x ∂μ)
      atTop (𝓝 (∫ x, f x * g x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => 4 * (‖f x‖ * ‖g x‖))
  · intro n
    exact (approx f hf n).aestronglyMeasurable.mul (approx g hg n).aestronglyMeasurable
  · exact (hf2.norm.integrable_mul hg2.norm).const_mul 4
  · intro n
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul]
    calc
      _ ≤ (2 * ‖f x‖) * (2 * ‖g x‖) :=
        mul_le_mul (norm_approx_le f hf n x) (norm_approx_le g hg n x)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · exact Filter.Eventually.of_forall (fun x => (tendsto_approx f hf x).mul (tendsto_approx g hg x))

theorem tendsto_integral_sq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 μ) :
    Tendsto (fun n => ∫ x, (approx f hf n x) ^ 2 ∂μ) atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
  simpa only [pow_two] using tendsto_integral_mul μ f f hf hf hf2 hf2

theorem tendsto_covariance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) :
    Tendsto (fun n => cov[approx f hf n, approx g hg n; μ]) atTop (𝓝 cov[f, g; μ]) := by
  simp_rw [covariance_eq_sub (memLp_approx μ f hf hf2 _) (memLp_approx μ g hg hg2 _),
    covariance_eq_sub hf2 hg2]
  exact (tendsto_integral_mul μ f g hf hg hf2 hg2).sub
    ((tendsto_integral μ f hf hf2).mul (tendsto_integral μ g hg hg2))

end SimpleApproximation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology

namespace MeasurableCovariance

variable {Ω : Type*} [MeasurableSpace Ω]

theorem abs_covariance_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) (phi : ℝ) (hphi : 0 ≤ phi)
    (hmix : ∀ (S T : Set ℝ), MeasurableSet S → MeasurableSet T →
      |μ.real (f ⁻¹' S ∩ g ⁻¹' T) - μ.real (f ⁻¹' S) * μ.real (g ⁻¹' T)| ≤
        phi * μ.real (f ⁻¹' S)) :
    |cov[f, g; μ]| ≤ 2 * Real.sqrt phi *
      (Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ)) := by
  have hn (n : ℕ) := SimpleCovariance.abs_covariance_le μ
    (SimpleApproximation.approx f hf n) (SimpleApproximation.approx g hg n) phi hphi
      (fun S T => hmix
        ((SimpleApproximation.approx (id : ℝ → ℝ) measurable_id n) ⁻¹' S)
        ((SimpleApproximation.approx (id : ℝ → ℝ) measurable_id n) ⁻¹' T)
        ((SimpleApproximation.approx (id : ℝ → ℝ) measurable_id n).measurableSet_preimage S)
        ((SimpleApproximation.approx (id : ℝ → ℝ) measurable_id n).measurableSet_preimage T))
  apply le_of_tendsto_of_tendsto'
    (SimpleApproximation.tendsto_covariance μ f g hf hg hf2 hg2).abs
    ((tendsto_const_nhds.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.sqrt phi) atTop _)).mul
      ((SimpleApproximation.tendsto_integral_sq μ f hf hf2).sqrt.mul
        (SimpleApproximation.tendsto_integral_sq μ g hg hg2).sqrt))
  exact hn

end MeasurableCovariance

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal ProbabilityTheory

namespace PhiEvents

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

theorem nonneg (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    0 ≤ phiMixingCoef P Y n := by
  simpa using indicator_cov_le_phi P Y n 0 Set.univ Set.univ
    MeasurableSet.univ (by simp) MeasurableSet.univ

theorem conditional_diff_le_one (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Set Ω) (hA : P A ≠ 0) :
    |P.real (A ∩ B) / P.real A - P.real B| ≤ 1 := by
  have hpos : 0 < P.real A := ENNReal.toReal_pos hA (measure_ne_top P A)
  have hratio : P.real (A ∩ B) / P.real A ≤ 1 := by
    apply (div_le_one hpos).mpr
    exact measureReal_mono Set.inter_subset_left (measure_ne_top P A)
  have hB : P.real B ≤ 1 := by
    simpa using measureReal_mono (Set.subset_univ B) (measure_ne_top P Set.univ)
  have hn : 0 ≤ P.real (A ∩ B) / P.real A := div_nonneg (measureReal_nonneg) (measureReal_nonneg)
  rw [abs_le]
  constructor <;> linarith [measureReal_nonneg (μ := P) (s := B)]

theorem weighted_event (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (n k : ℕ) (A B : Set Ω)
    (hA : MeasurableSet[processSigma Y (Set.Iic k)] A)
    (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) :
    |P.real (A ∩ B) - P.real A * P.real B| ≤ phiMixingCoef P Y n * P.real A := by
  by_cases hA0 : P A = 0
  · have hi : P (A ∩ B) = 0 := measure_mono_null Set.inter_subset_left hA0
    simp [measureReal_def, hA0, hi]
  have hbdd : BddAbove {r : ℝ | ∃ k' : ℕ, ∃ A' B' : Set Ω,
      MeasurableSet[processSigma Y (Set.Iic k')] A' ∧ P A' ≠ 0 ∧
      MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
      r = |P.real (A' ∩ B') / P.real A' - P.real B'|} := by
    refine ⟨1, ?_⟩
    rintro r ⟨k', A', B', _, hA', _, rfl⟩
    exact conditional_diff_le_one P A' B' hA'
  have hr : |P.real (A ∩ B) / P.real A - P.real B| ≤ phiMixingCoef P Y n := by
    exact le_csSup hbdd ⟨k, A, B, hA, hA0, hB, rfl⟩
  have hpos : 0 < P.real A := ENNReal.toReal_pos hA0 (measure_ne_top P A)
  have hfactor : P.real (A ∩ B) - P.real A * P.real B =
      (P.real (A ∩ B) / P.real A - P.real B) * P.real A := by
    field_simp
  rw [hfactor, abs_mul, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_right hr hpos.le

end PhiEvents

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal ProbabilityTheory

namespace PhiJointLaw

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

theorem weighted_event (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (n k : ℕ) (U V : Ω → ℝ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (hU2 : MemLp U 2 P) (hV2 : MemLp V 2 P)
    (S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    let μ := P.map (fun ω => (U ω, V ω))
    |μ.real (Prod.fst ⁻¹' S ∩ Prod.snd ⁻¹' T) -
      μ.real (Prod.fst ⁻¹' S) * μ.real (Prod.snd ⁻¹' T)| ≤
        phiMixingCoef P Y n * μ.real (Prod.fst ⁻¹' S) := by
  have hpair : AEMeasurable (fun ω => (U ω, V ω)) P := hU2.aemeasurable.prodMk hV2.aemeasurable
  dsimp only
  rw [map_measureReal_apply_of_aemeasurable hpair ((hS.preimage measurable_fst).inter
        (hT.preimage measurable_snd)),
    map_measureReal_apply_of_aemeasurable hpair (hS.preimage measurable_fst),
    map_measureReal_apply_of_aemeasurable hpair (hT.preimage measurable_snd)]
  exact PhiEvents.weighted_event P Y n k (U ⁻¹' S) (V ⁻¹' T) (hU hS) (hV hT)

theorem memLp_fst (P : Measure Ω) (U V : Ω → ℝ)
    (hU2 : MemLp U 2 P) (hV2 : MemLp V 2 P) :
    MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 (P.map (fun ω => (U ω, V ω))) := by
  have hpair := hU2.aemeasurable.prodMk hV2.aemeasurable
  exact (memLp_map_measure_iff measurable_fst.aestronglyMeasurable hpair).mpr hU2

theorem memLp_snd (P : Measure Ω) (U V : Ω → ℝ)
    (hU2 : MemLp U 2 P) (hV2 : MemLp V 2 P) :
    MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 (P.map (fun ω => (U ω, V ω))) := by
  have hpair := hU2.aemeasurable.prodMk hV2.aemeasurable
  exact (memLp_map_measure_iff measurable_snd.aestronglyMeasurable hpair).mpr hV2

theorem covariance_fst_snd (P : Measure Ω) (U V : Ω → ℝ)
    (hU2 : MemLp U 2 P) (hV2 : MemLp V 2 P) :
    cov[Prod.fst, Prod.snd; P.map (fun ω => (U ω, V ω))] = cov[U, V; P] :=
  covariance_map measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
    (hU2.aemeasurable.prodMk hV2.aemeasurable)

theorem integral_fst_sq (P : Measure Ω) (U V : Ω → ℝ)
    (hU2 : MemLp U 2 P) (hV2 : MemLp V 2 P) :
    (∫ z : ℝ × ℝ, z.1 ^ 2 ∂P.map (fun ω => (U ω, V ω))) = ∫ ω, U ω ^ 2 ∂P :=
  integral_map (hU2.aemeasurable.prodMk hV2.aemeasurable)
    (measurable_fst.pow_const 2).aestronglyMeasurable

theorem integral_snd_sq (P : Measure Ω) (U V : Ω → ℝ)
    (hU2 : MemLp U 2 P) (hV2 : MemLp V 2 P) :
    (∫ z : ℝ × ℝ, z.2 ^ 2 ∂P.map (fun ω => (U ω, V ω))) = ∫ ω, V ω ^ 2 ∂P :=
  integral_map (hU2.aemeasurable.prodMk hV2.aemeasurable)
    (measurable_snd.pow_const 2).aestronglyMeasurable

end PhiJointLaw

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ) (U V : Ω → ℝ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (hU2 : MemLp U 2 P) (hV2 : MemLp V 2 P) :
    |cov[U, V; P]| ≤ 2 * Real.sqrt (phiMixingCoef P Y n) *
      (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) := by
  let Uc : Ω → ℝ := fun ω => U ω - ∫ x, U x ∂P
  let Vc : Ω → ℝ := fun ω => V ω - ∫ x, V x ∂P
  have hUc : Measurable[processSigma Y (Set.Iic k)] Uc := hU.sub measurable_const
  have hVc : Measurable[processSigma Y (Set.Ici (k + n))] Vc := hV.sub measurable_const
  have hUc2 : MemLp Uc 2 P := hU2.sub (memLp_const _)
  have hVc2 : MemLp Vc 2 P := hV2.sub (memLp_const _)
  let μ := P.map (fun ω => (Uc ω, Vc ω))
  have hpair : AEMeasurable (fun ω => (Uc ω, Vc ω)) P := hUc2.aemeasurable.prodMk hVc2.aemeasurable
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hpair
  have h := MeasurableCovariance.abs_covariance_le μ Prod.fst Prod.snd
    measurable_fst measurable_snd (PhiJointLaw.memLp_fst P Uc Vc hUc2 hVc2)
    (PhiJointLaw.memLp_snd P Uc Vc hUc2 hVc2) (phiMixingCoef P Y n) (PhiEvents.nonneg P Y n)
    (PhiJointLaw.weighted_event P Y n k Uc Vc hUc hVc hUc2 hVc2)
  rw [PhiJointLaw.covariance_fst_snd P Uc Vc hUc2 hVc2,
    PhiJointLaw.integral_fst_sq P Uc Vc hUc2 hVc2,
    PhiJointLaw.integral_snd_sq P Uc Vc hUc2 hVc2] at h
  have hcov : cov[Uc, Vc; P] = cov[U, V; P] := by
    dsimp only [Uc, Vc]
    rw [covariance_sub_const_left (hU2.integrable one_le_two),
      covariance_sub_const_right (hV2.integrable one_le_two)]
  rw [hcov] at h
  simpa only [variance_eq_integral hU2.aemeasurable, variance_eq_integral hV2.aemeasurable] using h

#print axioms solution
