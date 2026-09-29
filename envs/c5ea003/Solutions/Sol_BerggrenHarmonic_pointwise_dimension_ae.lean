-- Prove2me | solution 1 for BerggrenHarmonic.pointwise_dimension_ae
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T13:25:16.330902+00:00
-- url     : https://prove2.me/submissions/6090a8fc-2643-4fa4-bb4a-37ddd400740d

-- Sol generated from Bridges/BerggrenBoundaryEntropy.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenBoundaryEntropy
import Definitions.Def_Bridges_BerggrenHarmonicMeasure
import Theorems.Thm_BerggrenHarmonic_ProbVec_pmf_apply
import Theorems.Thm_BerggrenHarmonic_bernoulli_cyl

/-!
# Entropy and dimension of the harmonic measure on the Berggren boundary

Building on `Catalog.Bridges.BerggrenHarmonicMeasure`, where the harmonic measure of the
Berggren random walk was identified with the Bernoulli product measure `bernoulli P` on the
3-adic boundary `Bdry = ℕ → Fin 3`, this file computes its **entropy** and its **pointwise
(Billingsley) dimension**.

## Main results

* `shannon` : the Shannon entropy `H(p₁,p₂,p₃) = -∑ pₐ log pₐ` of the step distribution.
* `expected_surprisal` : the *exact* level-`n` identity
  `∑_{w ∈ {1,2,3}ⁿ} μ[w] · (-log μ[w]) = n · H(p)`.  The mean surprisal of a depth-`n`
  cylinder is exactly `n H(p)` — no error term.
* `shannon_le_log_three`, `shannon_eq_log_three_iff` : `H(p) ≤ log 3` with equality exactly
  for the fair walk, so the harmonic measure has full dimension iff the three Berggren moves
  are equally likely.
* `strongLaw_surprisal`, `smb_ae` : the Shannon–McMillan–Breiman theorem for the Berggren
  boundary: `μ`-almost every boundary point `x` satisfies `-(1/n) log μ(cyl n x) → H(p)`.
* `pointwise_dimension_ae` : consequently the pointwise dimension of the harmonic measure
  with respect to the natural 3-adic metric (`diam (cyl n x) = 3⁻ⁿ`) is almost surely the
  constant `dimH P = H(p)/log 3 ∈ (0, 1]`.
* `dim_le_one`, `dim_uniform_eq_one`, `dim_eq_one_iff` : the dimension is at most `1`, the
  dimension of the whole 3-adic Cantor boundary, with equality iff the walk is fair.
-/

open BerggrenHarmonic

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

/-! ## Surprisal and Shannon entropy -/



lemma shannon_eq_sum_surp (P : ProbVec) : shannon P = ∑ a, P.p a * surp P a := by
  unfold shannon surp
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring










/-! ## Cylinder masses in the reals -/



/-- The harmonic measure of a cylinder, as a real number. -/
lemma bernoulli_cyl_toReal (P : ProbVec) (n : ℕ) (v : Bdry) :
    (bernoulli P (cyl n v)).toReal = massR P n v := by
  rw [bernoulli_cyl, wmass, ENNReal.toReal_prod, massR]
  exact Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal (P.pos (v i)).le

/-- The surprisal of a cylinder is the sum of the surprisals of its letters. -/
lemma neg_log_massR (P : ProbVec) (n : ℕ) (v : Bdry) :
    -Real.log (massR P n v) = ∑ i ∈ Finset.range n, surp P (v i) := by
  rw [massR, Real.log_prod (fun i _ => (P.pos (v i)).ne'), ← Finset.sum_neg_distrib]
  rfl

/-! ## The exact level-`n` entropy identity -/



/-! ## Shannon–McMillan–Breiman on the Berggren boundary -/

lemma measurable_letter_coord (g : Letter → ℝ) (i : ℕ) :
    Measurable (fun x : Bdry => g (x i)) :=
  (Measurable.of_discrete (f := g)).comp (measurable_pi_apply i)

lemma integrable_letter_coord (P : ProbVec) (g : Letter → ℝ) (i : ℕ) :
    Integrable (fun x : Bdry => g (x i)) (bernoulli P) := by
  refine Integrable.mono' (integrable_const (∑ a, |g a|))
    (measurable_letter_coord g i).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun a _ => abs_nonneg (g a)) (Finset.mem_univ (x i))

lemma integral_letter_coord (P : ProbVec) (g : Letter → ℝ) (i : ℕ) :
    ∫ x, g (x i) ∂(bernoulli P) = ∑ a, P.p a * g a := by
  have hmap : (bernoulli P).map (Function.eval i) = P.stepMeasure :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => P.stepMeasure) i).map_eq
  have h1 : ∫ a, g a ∂(P.stepMeasure) = ∫ x, g (x i) ∂(bernoulli P) := by
    rw [← hmap, integral_map (measurable_pi_apply i).aemeasurable
      (Measurable.of_discrete (f := g)).aestronglyMeasurable]
  rw [← h1, ProbVec.stepMeasure, PMF.integral_eq_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ProbVec.pmf_apply, ENNReal.toReal_ofReal (P.pos a).le, smul_eq_mul]

lemma iIndepFun_letters (P : ProbVec) (g : Letter → ℝ) :
    iIndepFun (fun (i : ℕ) (x : Bdry) => g (x i)) (bernoulli P) :=
  iIndepFun_infinitePi (X := fun _ : ℕ => g) (fun _ => Measurable.of_discrete)

lemma map_letter_coord (P : ProbVec) (g : Letter → ℝ) (i : ℕ) :
    (bernoulli P).map (fun x : Bdry => g (x i)) = P.stepMeasure.map g := by
  have hi : (bernoulli P).map (fun x : Bdry => x i) = P.stepMeasure :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => P.stepMeasure) i).map_eq
  have hcomp : (fun x : Bdry => g (x i)) = g ∘ (fun x : Bdry => x i) := rfl
  rw [hcomp, ← Measure.map_map (Measurable.of_discrete (f := g)) (measurable_pi_apply i), hi]

lemma identDistrib_letters (P : ProbVec) (g : Letter → ℝ) (i : ℕ) :
    IdentDistrib (fun x : Bdry => g (x i)) (fun x : Bdry => g (x 0))
      (bernoulli P) (bernoulli P) where
  aemeasurable_fst := (measurable_letter_coord g i).aemeasurable
  aemeasurable_snd := (measurable_letter_coord g 0).aemeasurable
  map_eq := by rw [map_letter_coord, map_letter_coord]

/-- **The strong law of large numbers for the letters of a random Berggren word.**  For every
observable `g` of a single Berggren move, the empirical average of `g` along almost every
infinite word converges to its mean `∑ₐ pₐ g(a)`. -/
theorem strongLaw_letters (P : ProbVec) (g : Letter → ℝ) :
    ∀ᵐ x ∂(bernoulli P),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, g (x i)) / n) atTop
        (𝓝 (∑ a, P.p a * g a)) := by
  have h := ProbabilityTheory.strong_law_ae_real
    (fun (i : ℕ) (x : Bdry) => g (x i)) (integrable_letter_coord P g 0)
    (fun i j hij => (iIndepFun_letters P g).indepFun hij) (identDistrib_letters P g)
  rw [integral_letter_coord P g 0] at h
  exact h

/-- **The strong law for the surprisal.**  Almost every infinite Berggren word has average
surprisal converging to the Shannon entropy of the step distribution. -/
theorem strongLaw_surprisal (P : ProbVec) :
    ∀ᵐ x ∂(bernoulli P),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, surp P (x i)) / n) atTop
        (𝓝 (shannon P)) := by
  have h := strongLaw_letters P (surp P)
  rwa [← shannon_eq_sum_surp] at h

/-- **Shannon–McMillan–Breiman for the harmonic measure of the Berggren walk.**  For almost
every boundary point, the harmonic measure of the depth-`n` cylinder through it decays like
`e^{-n H(p)}`. -/
theorem smb_ae (P : ProbVec) :
    ∀ᵐ x ∂(bernoulli P),
      Tendsto (fun n : ℕ => -Real.log ((bernoulli P (cyl n x)).toReal) / n) atTop
        (𝓝 (shannon P)) := by
  filter_upwards [strongLaw_surprisal P] with x hx
  have hfun : ∀ n : ℕ, -Real.log ((bernoulli P (cyl n x)).toReal) / n
      = (∑ i ∈ Finset.range n, surp P (x i)) / n := by
    intro n
    rw [bernoulli_cyl_toReal, neg_log_massR]
  simpa only [hfun] using hx

/-! ## Dimension -/









open BerggrenHarmonic in
theorem solution(P : ProbVec) :
    ∀ᵐ x ∂(bernoulli P),
      Tendsto (fun n : ℕ =>
          Real.log ((bernoulli P (cyl n x)).toReal) / Real.log ((3 : ℝ) ^ (-(n : ℝ)))) atTop
        (𝓝 (dimH P)) := by
  filter_upwards [smb_ae P] with x hx
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hfun : ∀ n : ℕ, n ≠ 0 →
      Real.log ((bernoulli P (cyl n x)).toReal) / Real.log ((3 : ℝ) ^ (-(n : ℝ)))
        = (-Real.log ((bernoulli P (cyl n x)).toReal) / n) / Real.log 3 := by
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [Real.log_rpow (by norm_num)]
    field_simp
  have := hx.div_const (Real.log 3)
  rw [show dimH P = shannon P / Real.log 3 by rfl]
  refine Tendsto.congr' ?_ this
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (hfun n hn.ne').symm
