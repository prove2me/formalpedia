-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_asymptotic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:39:26.595292+00:00
-- url     : https://prove2.me/submissions/fa2cb401-8005-41ac-8c14-0b40bf873559

import Definitions.Def_LinearBanditProtocol
import Definitions.Def_ConsistentBanditPolicy
import Theorems.Thm_BanditAlgorithm_bandit_divergence_decomposition
import Theorems.Thm_BanditAlgorithm_gaussian_relative_entropy_formula
import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality
import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_bandit_canonical_occupation_identities
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

/-! Asymptotic lower bounds for finite Gaussian linear bandits.
Lattimore and Szepesvari, Bandit Algorithms, Theorem 25.1 and Corollary 25.2.
Complete attributed local proof components follow; no open target is imported. -/

/- Component: FixedAlternativeInformation. -/
section
/-!
Fixed-alternative information for finite Gaussian linear bandits.
Source: Lattimore and Szepesvari, Bandit Algorithms, Chapter 25,
especially equations (25.2)--(25.3). Count-measurability and Gaussian
integrability arguments adapt the complete accepted GaussianFixedGapTesting
proof (93adfc89-7beb-45fe-8ae0-1d1ac44291d4, submission
36f73619-8000-4baa-8ca6-ceb56c9e144d), with its upstream attribution retained
in probability-source-provenance.json. All adapted helper bodies are included.
-/

open Matrix MeasureTheory ProbabilityTheory InformationTheory Filter BanditAlgorithm
open scoped Topology

namespace AsymptoticLinearBandit

noncomputable def expectedPulls {k : ℕ} (nu : StochasticBandit k)
    (pi : BanditPolicy k) (n : ℕ) (j : Fin k) : ℝ :=
  ∫ h, (armPullCount j h : ℝ) ∂banditMeasure nu pi n

theorem expected_pull_nonneg {k : ℕ} (nu : StochasticBandit k)
    (pi : BanditPolicy k) (n : ℕ) (j : Fin k) : 0 ≤ expectedPulls nu pi n j :=
  integral_nonneg fun _ => Nat.cast_nonneg _

theorem measurable_pullCount {k n : ℕ} (j : Fin k) :
    Measurable (fun h : BanditHistory k n => (armPullCount j h : ℝ)) := by
  classical
  have heq : (fun h : BanditHistory k n => (armPullCount j h : ℝ)) =
      fun h => ∑ t, if (h t).1 = j then (1 : ℝ) else 0 := by
    funext h
    rw [armPullCount]
    have hs : {t | (h t).1 = j}.toFinset =
        Finset.univ.filter (fun t => (h t).1 = j) := by ext t; simp
    rw [hs]
    simp
  rw [heq]
  exact Finset.measurable_sum Finset.univ fun t _ => Measurable.ite
    ((measurableSet_singleton j).preimage
      (measurable_fst.comp (measurable_pi_apply t))) measurable_const measurable_const

theorem pullCount_le {k n : ℕ} (j : Fin k) (h : BanditHistory k n) :
    (armPullCount j h : ℝ) ≤ n := by
  exact_mod_cast (show armPullCount j h ≤ n by
    rw [armPullCount]
    simpa using (Finset.card_le_univ {t | (h t).1 = j}.toFinset))

theorem integrable_pullCount {k n : ℕ} (nu : StochasticBandit k)
    (pi : BanditPolicy k) (j : Fin k) :
    Integrable (fun h : BanditHistory k n => (armPullCount j h : ℝ))
      (banditMeasure nu pi n) := by
  have h := Integrable.bdd_mul
    (integrable_const (μ := banditMeasure nu pi n) (1 : ℝ))
    (measurable_pullCount (n := n) j).aestronglyMeasurable
    (c := (n : ℝ)) (by
      filter_upwards [] with h
      rw [norm_natCast]
      exact pullCount_le j h)
  simpa only [mul_one] using h

theorem gaussian_integrable {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (j : Fin k) :
    Integrable id ((gaussianLinearBandit arms theta).P j) := by
  apply memLp_one_iff_integrable.mp
  simpa [gaussianLinearBandit, gaussianBandit] using
    (ProbabilityTheory.memLp_id_gaussianReal'
      (μ := arms j ⬝ᵥ theta) (v := (1 : NNReal)) (1 : ENNReal) (by simp))

theorem gaussian_mean {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (j : Fin k) :
    banditArmMean (gaussianLinearBandit arms theta) j = arms j ⬝ᵥ theta := by
  simp [banditArmMean, gaussianLinearBandit, gaussianBandit]

theorem gaussian_gap {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (j : Fin k) :
    banditGap (gaussianLinearBandit arms theta) j = linearArmGap arms theta j := by
  simp [banditGap, banditOptimalMean, linearArmGap, gaussian_mean]

theorem linear_gap_nonneg {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (j : Fin k) : 0 ≤ linearArmGap arms theta j := by
  exact sub_nonneg.mpr (le_ciSup (Set.finite_range (fun i => arms i ⬝ᵥ theta)).bddAbove j)

theorem sum_expected_pulls_eq_n {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) :
    ∑ j, expectedPulls (gaussianLinearBandit arms theta) pi n j = n :=
  (bandit_canonical_occupation_identities _ (gaussian_integrable arms theta) pi n).2

theorem regret_eq_sum {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) :
    banditRegret (gaussianLinearBandit arms theta) pi n =
      ∑ j, linearArmGap arms theta j *
        expectedPulls (gaussianLinearBandit arms theta) pi n j := by
  simpa only [gaussian_gap, expectedPulls] using
    bandit_regret_decomposition _ (gaussian_integrable arms theta) pi n

theorem regret_nonneg {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) :
    0 ≤ banditRegret (gaussianLinearBandit arms theta) pi n := by
  rw [regret_eq_sum]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (linear_gap_nonneg arms theta j) (expected_pull_nonneg _ pi n j)

theorem gaussian_arm_kl {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta theta' : Fin d → ℝ) (j : Fin k) :
    klDiv ((gaussianLinearBandit arms theta).P j)
      ((gaussianLinearBandit arms theta').P j) =
        ENNReal.ofReal ((arms j ⬝ᵥ (theta' - theta)) ^ 2 / 2) := by
  rw [show (gaussianLinearBandit arms theta).P j = gaussianReal (arms j ⬝ᵥ theta) 1 by rfl,
    show (gaussianLinearBandit arms theta').P j = gaussianReal (arms j ⬝ᵥ theta') 1 by rfl,
    gaussian_relative_entropy_formula _ _ (by norm_num)]
  congr 1
  simp only [NNReal.coe_one, mul_one, dotProduct_sub]
  ring

theorem gaussian_kl_sum {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta theta' : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) :
    klDiv (banditMeasure (gaussianLinearBandit arms theta) pi n)
      (banditMeasure (gaussianLinearBandit arms theta') pi n) =
        ENNReal.ofReal (∑ j, expectedPulls (gaussianLinearBandit arms theta) pi n j *
          ((arms j ⬝ᵥ (theta' - theta)) ^ 2 / 2)) := by
  have hfin (j : Fin k) : klDiv ((gaussianLinearBandit arms theta).P j)
      ((gaussianLinearBandit arms theta').P j) ≠ ⊤ := by
    rw [gaussian_arm_kl]
    exact ENNReal.ofReal_ne_top
  rw [bandit_divergence_decomposition _ _ hfin pi n]
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
    mul_nonneg (expected_pull_nonneg _ pi n j) (by positivity)]
  apply Finset.sum_congr rfl
  intro j _
  rw [gaussian_arm_kl]
  exact (ENNReal.ofReal_mul (expected_pull_nonneg _ pi n j)).symm

theorem gaussian_kl_ne_top {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta theta' : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) :
    klDiv (banditMeasure (gaussianLinearBandit arms theta) pi n)
      (banditMeasure (gaussianLinearBandit arms theta') pi n) ≠ ⊤ := by
  rw [gaussian_kl_sum]
  exact ENNReal.ofReal_ne_top

theorem design_quadratic_eq_sum {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) (v : Fin d → ℝ) :
    v ⬝ᵥ linearBanditExpectedDesign arms (gaussianLinearBandit arms theta) pi n *ᵥ v =
      ∑ j, expectedPulls (gaussianLinearBandit arms theta) pi n j * (arms j ⬝ᵥ v) ^ 2 := by
  simp only [linearBanditExpectedDesign, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, expectedPulls]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec, pow_two,
    Finset.mul_sum, mul_comm, mul_left_comm]

theorem gaussian_kl_quadratic {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta theta' : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) :
    (klDiv (banditMeasure (gaussianLinearBandit arms theta) pi n)
      (banditMeasure (gaussianLinearBandit arms theta') pi n)).toReal =
        ((theta' - theta) ⬝ᵥ
          linearBanditExpectedDesign arms (gaussianLinearBandit arms theta) pi n *ᵥ
            (theta' - theta)) / 2 := by
  rw [gaussian_kl_sum, ENNReal.toReal_ofReal (Finset.sum_nonneg fun j _ =>
    mul_nonneg (expected_pull_nonneg _ pi n j) (by positivity)), design_quadratic_eq_sum]
  simp only [Finset.sum_div, mul_div_assoc]

theorem regret_eq_expected_gap_sum {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) :
    banditRegret (gaussianLinearBandit arms theta) pi n =
      ∑ j, expectedPulls (gaussianLinearBandit arms theta) pi n j *
        linearArmGap arms theta j := by
  simpa only [mul_comm] using regret_eq_sum arms theta pi n

theorem unique_optimal_gap_lower {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (jstar : Fin k)
    (hopt : ∀ j, j ≠ jstar → arms j ⬝ᵥ theta < arms jstar ⬝ᵥ theta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ j, j ≠ jstar → eps ≤ linearArmGap arms theta j := by
  classical
  letI : Nonempty (Fin k) := ⟨jstar⟩
  let f : Fin k → ℝ := fun j => if j = jstar then 1 else
    arms jstar ⬝ᵥ theta - arms j ⬝ᵥ theta
  have hf (j : Fin k) : 0 < f j := by
    by_cases hj : j = jstar
    · simp [f, hj]
    · simpa [f, hj] using sub_pos.mpr (hopt j hj)
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨f i, hf i, ?_⟩
  intro j hj
  have hle := hmin j (Finset.mem_univ j)
  have hmax : arms jstar ⬝ᵥ theta ≤ ⨆ l, arms l ⬝ᵥ theta :=
    le_ciSup (Set.finite_range (fun l => arms l ⬝ᵥ theta)).bddAbove jstar
  simp only [f, if_neg hj] at hle
  unfold linearArmGap
  linarith

theorem regret_ge_missed_optimal {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) (jstar : Fin k)
    (eps : ℝ) (hgap : ∀ j, j ≠ jstar → eps ≤ linearArmGap arms theta j) :
    eps * ((n : ℝ) - expectedPulls (gaussianLinearBandit arms theta) pi n jstar) ≤
      banditRegret (gaussianLinearBandit arms theta) pi n := by
  classical
  let a := expectedPulls (gaussianLinearBandit arms theta) pi n
  have hsum : (∑ j ∈ Finset.univ.erase jstar, a j) + a jstar = n := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ jstar)]
    exact sum_expected_pulls_eq_n arms theta pi n
  change eps * ((n : ℝ) - a jstar) ≤ _
  rw [regret_eq_sum]
  calc
    eps * ((n : ℝ) - a jstar) = ∑ j ∈ Finset.univ.erase jstar, eps * a j := by
      rw [← Finset.mul_sum]
      congr 1
      linarith
    _ ≤ ∑ j ∈ Finset.univ.erase jstar, linearArmGap arms theta j * a j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right
        (hgap j (Finset.mem_erase.mp hj).1) (expected_pull_nonneg _ pi n j)
    _ ≤ ∑ j, linearArmGap arms theta j * a j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ =>
        mul_nonneg (linear_gap_nonneg arms theta j) (expected_pull_nonneg _ pi n j)

theorem regret_ge_arm {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) (j : Fin k)
    (eps : ℝ) (hgap : eps ≤ linearArmGap arms theta j) :
    eps * expectedPulls (gaussianLinearBandit arms theta) pi n j ≤
      banditRegret (gaussianLinearBandit arms theta) pi n := by
  rw [regret_eq_sum]
  refine (mul_le_mul_of_nonneg_right hgap (expected_pull_nonneg _ pi n j)).trans ?_
  exact Finset.single_le_sum (fun i _ =>
    mul_nonneg (linear_gap_nonneg arms theta i) (expected_pull_nonneg _ pi n i))
    (Finset.mem_univ j)

theorem optimal_expected_pulls_ge_half_eventually {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (pi : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {nu : StochasticBandit k | ∃ theta' : Fin d → ℝ, nu = gaussianLinearBandit arms theta'} pi)
    (theta : Fin d → ℝ) (jstar : Fin k)
    (hopt : ∀ j, j ≠ jstar → arms j ⬝ᵥ theta < arms jstar ⬝ᵥ theta) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 ≤
      expectedPulls (gaussianLinearBandit arms theta) pi n jstar := by
  obtain ⟨eps, heps, hgap⟩ := unique_optimal_gap_lower arms theta jstar hopt
  have hsmall := hcons (gaussianLinearBandit arms theta) ⟨theta, rfl⟩ 1 (by norm_num)
  simp only [Real.rpow_one] at hsmall
  have hevent := (tendsto_order.1 hsmall).2 (eps / 2) (by positivity)
  filter_upwards [hevent, eventually_ge_atTop 1] with n hn hnpos
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr := (div_lt_iff₀ hnreal).mp hn
  have hl := regret_ge_missed_optimal arms theta pi n jstar eps hgap
  nlinarith

private theorem integral_ge_event {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsFiniteMeasure P] {A : Set Omega} (hA : MeasurableSet A)
    (f : Omega → ℝ) (c : ℝ) (hf : Integrable f P)
    (hfc : ∀ x ∈ A, c ≤ f x) (hf0 : ∀ x, 0 ≤ f x) :
    P.real A * c ≤ ∫ x, f x ∂P := by
  have hi := (integrable_const (μ := P) c).indicator hA
  have hmono : ∫ x, A.indicator (fun _ : Omega => c) x ∂P ≤ ∫ x, f x ∂P := by
    apply integral_mono hi hf
    intro x
    by_cases hx : x ∈ A
    · simpa [Set.indicator_of_mem hx] using hfc x hx
    · simpa [Set.indicator, hx] using hf0 x
  simpa [integral_indicator_const, hA, smul_eq_mul] using hmono

theorem two_environment_testing {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta theta' : Fin d → ℝ) (pi : BanditPolicy k) (jstar : Fin k)
    (eps : ℝ) (heps : 0 < eps)
    (hgap : ∀ j, j ≠ jstar → eps ≤ linearArmGap arms theta j)
    (hgap' : eps ≤ linearArmGap arms theta' jstar) (n : ℕ) :
    Real.exp (-(klDiv (banditMeasure (gaussianLinearBandit arms theta) pi n)
      (banditMeasure (gaussianLinearBandit arms theta') pi n)).toReal) * (n : ℝ) * eps ≤
        4 * (banditRegret (gaussianLinearBandit arms theta) pi n +
          banditRegret (gaussianLinearBandit arms theta') pi n) := by
  let P := banditMeasure (gaussianLinearBandit arms theta) pi n
  let Q := banditMeasure (gaussianLinearBandit arms theta') pi n
  let A : Set (BanditHistory k n) := {h | (armPullCount jstar h : ℝ) < (n : ℝ) / 2}
  have hA : MeasurableSet A := measurableSet_lt (measurable_pullCount jstar) measurable_const
  have hP := integral_ge_event P hA
    (fun h => (n : ℝ) - (armPullCount jstar h : ℝ)) ((n : ℝ) / 2)
    ((integrable_const _).sub (integrable_pullCount _ pi jstar))
    (by intro h hh; change (armPullCount jstar h : ℝ) < (n : ℝ) / 2 at hh; linarith)
    (fun h => sub_nonneg.mpr (pullCount_le jstar h))
  have hQ := integral_ge_event Q hA.compl
    (fun h => (armPullCount jstar h : ℝ)) ((n : ℝ) / 2)
    (integrable_pullCount _ pi jstar)
    (by intro h hh; exact le_of_not_gt hh) (fun _ => Nat.cast_nonneg _)
  have hInt := integrable_pullCount (n := n) (gaussianLinearBandit arms theta) pi jstar
  rw [integral_sub (integrable_const _) hInt] at hP
  simp only [integral_const, probReal_univ, one_smul] at hP
  change P.real A * ((n : ℝ) / 2) ≤ (n : ℝ) -
    expectedPulls (gaussianLinearBandit arms theta) pi n jstar at hP
  change Q.real Aᶜ * ((n : ℝ) / 2) ≤
    expectedPulls (gaussianLinearBandit arms theta') pi n jstar at hQ
  have hR := (mul_le_mul_of_nonneg_left hP heps.le).trans
    (regret_ge_missed_optimal arms theta pi n jstar eps hgap)
  have hR' := (mul_le_mul_of_nonneg_left hQ heps.le).trans
    (regret_ge_arm arms theta' pi n jstar eps hgap')
  have hBH := bretagnolle_huber_inequality P Q hA
    (gaussian_kl_ne_top arms theta theta' pi n)
  have hmul := mul_le_mul_of_nonneg_left hBH
    (mul_nonneg (Nat.cast_nonneg n) heps.le)
  dsimp only [P, Q] at hmul hR hR'
  nlinarith

private theorem log_lower_of_testing
    (R S D : ℕ → ℝ) (eps : ℝ) (heps : 0 < eps)
    (hR : ∀ p : ℝ, 0 < p → Tendsto (fun n : ℕ => R n / (n : ℝ) ^ p) atTop (𝓝 0))
    (hS : ∀ p : ℝ, 0 < p → Tendsto (fun n : ℕ => S n / (n : ℝ) ^ p) atTop (𝓝 0))
    (htest : ∀ n, Real.exp (-D n) * (n : ℝ) * eps ≤ 4 * (R n + S n))
    (c : ℝ) (hc : c < 1) :
    ∀ᶠ n : ℕ in atTop, c * Real.log n ≤ D n := by
  let p : ℝ := (1 - c) / 2
  have hp : 0 < p := by dsimp [p]; linarith
  have hr := (tendsto_order.1 (hR p hp)).2 1 (by norm_num)
  have hs := (tendsto_order.1 (hS p hp)).2 1 (by norm_num)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  have hgrow := hpow.eventually (eventually_ge_atTop (8 / eps))
  filter_upwards [hr, hs, hgrow, eventually_ge_atTop 1] with n hnR hnS hnG hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hnpos _
  have hr' := (div_lt_iff₀ hnp).mp hnR
  have hs' := (div_lt_iff₀ hnp).mp hnS
  have hg' := (div_le_iff₀ heps).mp hnG
  have hbig : Real.exp (-D n) * (n : ℝ) * eps ≤
      ((n : ℝ) ^ p * (n : ℝ) ^ p) * eps := by
    have ht := htest n
    nlinarith
  have hcancel := (mul_le_mul_iff_left₀ heps).mp hbig
  have hpower : (n : ℝ) ^ p * (n : ℝ) ^ p =
      Real.exp (-(c * Real.log n)) * (n : ℝ) := by
    calc
      (n : ℝ) ^ p * (n : ℝ) ^ p = Real.exp (Real.log n * p + Real.log n * p) := by
        rw [Real.rpow_def_of_pos hnpos, Real.exp_add]
      _ = Real.exp (-(c * Real.log n) + Real.log n) := by
        congr 1
        dsimp [p]
        ring
      _ = Real.exp (-(c * Real.log n)) * (n : ℝ) := by rw [Real.exp_add, Real.exp_log hnpos]
  rw [hpower] at hcancel
  have hexp := (mul_le_mul_iff_left₀ hnpos).mp hcancel
  have := Real.exp_le_exp.mp hexp
  linarith

theorem information_lower_eventually {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (pi : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {nu : StochasticBandit k | ∃ theta' : Fin d → ℝ, nu = gaussianLinearBandit arms theta'} pi)
    (theta : Fin d → ℝ) (jstar : Fin k)
    (hopt : ∀ j, j ≠ jstar → arms j ⬝ᵥ theta < arms jstar ⬝ᵥ theta)
    (theta' : Fin d → ℝ)
    (hchange : ∃ j, arms jstar ⬝ᵥ theta' < arms j ⬝ᵥ theta') (c : ℝ) (hc : c < 1) :
    ∀ᶠ n : ℕ in atTop, c * Real.log n ≤
      (klDiv (banditMeasure (gaussianLinearBandit arms theta) pi n)
        (banditMeasure (gaussianLinearBandit arms theta') pi n)).toReal := by
  obtain ⟨delta, hdelta, hgap⟩ := unique_optimal_gap_lower arms theta jstar hopt
  have halt : 0 < linearArmGap arms theta' jstar := by
    obtain ⟨j, hj⟩ := hchange
    have hle := le_ciSup (Set.finite_range (fun i => arms i ⬝ᵥ theta')).bddAbove j
    unfold linearArmGap
    linarith
  let eps := min delta (linearArmGap arms theta' jstar)
  have heps : 0 < eps := lt_min hdelta halt
  apply log_lower_of_testing
    (fun n => banditRegret (gaussianLinearBandit arms theta) pi n)
    (fun n => banditRegret (gaussianLinearBandit arms theta') pi n)
    (fun n => (klDiv (banditMeasure (gaussianLinearBandit arms theta) pi n)
      (banditMeasure (gaussianLinearBandit arms theta') pi n)).toReal) eps heps
  · exact hcons _ ⟨theta, rfl⟩
  · exact hcons _ ⟨theta', rfl⟩
  · intro n
    exact two_environment_testing arms theta theta' pi jstar eps heps
      (fun j hj => (min_le_left _ _).trans (hgap j hj)) (min_le_right _ _) n
  · exact hc

theorem information_quadratic_eventually {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (pi : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {nu : StochasticBandit k | ∃ theta' : Fin d → ℝ, nu = gaussianLinearBandit arms theta'} pi)
    (theta : Fin d → ℝ) (jstar : Fin k)
    (hopt : ∀ j, j ≠ jstar → arms j ⬝ᵥ theta < arms jstar ⬝ᵥ theta)
    (v : Fin d → ℝ)
    (hchange : ∃ j, arms jstar ⬝ᵥ (theta + v) < arms j ⬝ᵥ (theta + v))
    (c : ℝ) (hc : c < 1) :
    ∀ᶠ n : ℕ in atTop, 2 * c * Real.log n ≤
      ∑ j, expectedPulls (gaussianLinearBandit arms theta) pi n j * (arms j ⬝ᵥ v) ^ 2 := by
  filter_upwards [information_lower_eventually arms pi hcons theta jstar hopt
    (theta + v) hchange c hc] with n hn
  rw [gaussian_kl_quadratic, design_quadratic_eq_sum] at hn
  simp only [add_sub_cancel_left] at hn
  linarith


end AsymptoticLinearBandit
end

/- Component: FrameGeometry. -/
section
open Matrix Filter
open scoped BigOperators

namespace AsymptoticLinearBandit

lemma finite_positive_lower_bound {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  classical
  suffices ∀ s : Finset I, ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, c ≤ f i by
    obtain ⟨c, hc, hb⟩ := this Finset.univ
    exact ⟨c, hc, fun i => hb i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨c, hc, hb⟩ := ih
      refine ⟨min c (f i), lt_min hc (hf i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hb j hj)

lemma linear_functional_dot {d : ℕ} (f : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (v : Fin d → ℝ) : f v = v ⬝ᵥ (fun i => f (Pi.single i 1)) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [dotProduct, map_sum]

lemma exists_annihilating_vector {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (s : Finset (Fin k))
    (hs : Submodule.span ℝ (arms '' (s : Set (Fin k))) ≠ ⊤) :
    ∃ v : Fin d → ℝ, v ≠ 0 ∧ ∀ j ∈ s, arms j ⬝ᵥ v = 0 := by
  classical
  obtain ⟨f, hf, hker⟩ :=
    (Submodule.span ℝ (arms '' (s : Set (Fin k)))).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hs)
  refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
  · intro h
    apply hf
    apply LinearMap.ext
    intro x
    change f x = 0
    rw [linear_functional_dot f x, h]
    simp
  · intro j hj
    rw [← linear_functional_dot]
    exact hker (Submodule.subset_span ⟨j, hj, rfl⟩)

lemma spanning_dot_separates {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (s : Finset (Fin k))
    (hs : Submodule.span ℝ (arms '' (s : Set (Fin k))) = ⊤)
    (v : Fin d → ℝ) (hv : ∀ j ∈ s, arms j ⬝ᵥ v = 0) : v = 0 := by
  have hall : ∀ x : Fin d → ℝ, x ⬝ᵥ v = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℝ (arms '' (s : Set (Fin k))) := by
      rw [hs]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        exact hv j hj
    | zero => simp
    | add x y hx hy ihx ihy => simp [add_dotProduct, ihx, ihy]
    | smul a x hx ih => simp [smul_dotProduct, ih]
  exact dotProduct_self_eq_zero.mp (hall v)

lemma spanning_frame_lower_bound {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (s : Finset (Fin k))
    (hs : Submodule.span ℝ (arms '' (s : Set (Fin k))) = ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin d → ℝ,
      c * (v ⬝ᵥ v) ≤ ∑ j ∈ s, (arms j ⬝ᵥ v) ^ 2 := by
  classical
  let f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ s :=
    { toFun := fun v => WithLp.toLp 2 (fun j => arms j ⬝ᵥ v)
      map_add' := by intro v w; ext j; simp [dotProduct_add]
      map_smul' := by intro a v; ext j; simp [dotProduct_smul] }
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply (LinearMap.ker_eq_bot').mpr
    intro v hv
    apply WithLp.ofLp_injective 2
    change v.ofLp = 0
    apply spanning_dot_separates arms s hs
    intro j hj
    have h := congrArg (fun w : EuclideanSpace ℝ s => w ⟨j, hj⟩) hv
    exact h
  obtain ⟨K, hK, hanti⟩ := f.injective_iff_antilipschitz.mp hf
  have hKr : (0 : ℝ) < K := hK
  refine ⟨((K : ℝ) ^ 2)⁻¹, by positivity, ?_⟩
  intro v
  have hb := hanti.le_mul_norm (map_zero f) (WithLp.toLp 2 v)
  have hb2 : ‖WithLp.toLp 2 v‖ ^ 2 ≤ (K : ℝ) ^ 2 *
      ‖f (WithLp.toLp 2 v)‖ ^ 2 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 v), norm_nonneg (f (WithLp.toLp 2 v))]
  have hvnorm : ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
    rw [EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v)]
    simp [dotProduct, pow_two]
  have hfnorm : ‖f (WithLp.toLp 2 v)‖ ^ 2 =
      ∑ j ∈ s, (arms j ⬝ᵥ v) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j : s, (arms j ⬝ᵥ v) ^ 2) = ∑ j ∈ s, (arms j ⬝ᵥ v) ^ 2
    exact Finset.sum_coe_sort s (fun j => (arms j ⬝ᵥ v) ^ 2)
  rw [hvnorm, hfnorm] at hb2
  exact (inv_mul_le_iff₀ (sq_pos_of_pos hKr)).mpr hb2

lemma proper_subset_alternative {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (θ : Fin d → ℝ) (star : Fin k) (s : Finset (Fin k)) (hstar : star ∈ s)
    (hs : Submodule.span ℝ (arms '' (s : Set (Fin k))) ≠ ⊤) :
    ∃ u : Fin d → ℝ, (∀ j ∈ s, arms j ⬝ᵥ u = 0) ∧
      ∃ j : Fin k, arms star ⬝ᵥ (θ + u) < arms j ⬝ᵥ (θ + u) := by
  classical
  obtain ⟨v, hv, hz⟩ := exists_annihilating_vector arms s hs
  have hex : ∃ j, arms j ⬝ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply spanning_dot_separates arms Finset.univ
    · simpa using hspan
    · exact fun j _ => h j
  obtain ⟨j, hj⟩ := hex
  let t : ℝ := (arms star ⬝ᵥ θ - arms j ⬝ᵥ θ + 1) / (arms j ⬝ᵥ v)
  refine ⟨t • v, ?_, j, ?_⟩
  · intro i hi
    simp [dotProduct_smul, hz i hi]
  · have hstarzero := hz star hstar
    have ht : t * (arms j ⬝ᵥ v) = arms star ⬝ᵥ θ - arms j ⬝ᵥ θ + 1 := by
      exact div_mul_cancel₀ _ hj
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hstarzero, mul_zero,
      add_zero]
    nlinarith

lemma outer_design_quadratic {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (w : Fin k → ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ (∑ j : Fin k, w j • vecMulVec (arms j) (arms j)) *ᵥ v =
      ∑ j : Fin k, w j * (arms j ⬝ᵥ v) ^ 2 := by
  simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec, pow_two,
    Finset.mul_sum, mul_comm, mul_left_comm]

lemma outer_design_posDef_of_lower_bound {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (w : Fin k → ℝ) (c : ℝ) (hc : 0 < c)
    (hb : ∀ v : Fin d → ℝ,
      c * (v ⬝ᵥ v) ≤ ∑ j : Fin k, w j * (arms j ⬝ᵥ v) ^ 2) :
    (∑ j : Fin k, w j • vecMulVec (arms j) (arms j)).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, star_trivial]
    apply Finset.sum_congr rfl
    intro t _
    ring
  · intro v hv
    have hvpos : 0 < v ⬝ᵥ v := by
      simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hv
    simpa only [star_trivial, outer_design_quadratic] using
      (mul_pos hc hvpos).trans_le (hb v)


end AsymptoticLinearBandit
end

/- Component: NondegenerateDesign. -/
section
open Matrix Filter
open scoped BigOperators

namespace AsymptoticLinearBandit

/-- A finite family is uniformly coercive once every proper subspace eventually
misses an arm whose weight is uniformly at least a positive scale multiple. -/
lemma finite_frame_eventual_lower_bound {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (w : ℕ → Fin k → ℝ) (scale : ℕ → ℝ)
    (hw : ∀ n j, 0 ≤ w n j)
    (hscale : ∀ᶠ n : ℕ in atTop, 0 ≤ scale n)
    (hmiss : ∀ s : Finset (Fin k),
      Submodule.span ℝ (arms '' (s : Set (Fin k))) ≠ ⊤ →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
        ∃ j : Fin k, j ∉ s ∧ c * scale n ≤ w n j) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ v : Fin d → ℝ,
      c * scale n * (v ⬝ᵥ v) ≤
        ∑ j : Fin k, w n j * (arms j ⬝ᵥ v) ^ 2 := by
  classical
  have hm : ∀ s : Finset (Fin k), ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        Submodule.span ℝ (arms '' (s : Set (Fin k))) ≠ ⊤ →
          ∃ j : Fin k, j ∉ s ∧ c * scale n ≤ w n j := by
    intro s
    by_cases hs : Submodule.span ℝ (arms '' (s : Set (Fin k))) = ⊤
    · exact ⟨1, by norm_num, Filter.Eventually.of_forall (by simp [hs])⟩
    · obtain ⟨c, hc, he⟩ := hmiss s hs
      exact ⟨c, hc, he.mono fun n hn _ => hn⟩
  choose c hc he using hm
  obtain ⟨δ, hδ, hδc⟩ := finite_positive_lower_bound c hc
  have hf : ∀ s : Finset (Fin k), ∃ b : ℝ, 0 < b ∧
      (Submodule.span ℝ (arms '' (s : Set (Fin k))) = ⊤ →
        ∀ v : Fin d → ℝ, b * (v ⬝ᵥ v) ≤ ∑ j ∈ s, (arms j ⬝ᵥ v) ^ 2) := by
    intro s
    by_cases hs : Submodule.span ℝ (arms '' (s : Set (Fin k))) = ⊤
    · obtain ⟨b, hb, hbound⟩ := spanning_frame_lower_bound arms s hs
      exact ⟨b, hb, fun _ => hbound⟩
    · exact ⟨1, by norm_num, by simp [hs]⟩
  choose b hb hbound using hf
  obtain ⟨β, hβ, hβb⟩ := finite_positive_lower_bound b hb
  refine ⟨δ * β, mul_pos hδ hβ, ?_⟩
  filter_upwards [Filter.eventually_all.2 he, hscale] with n hn hnscale
  let s : Finset (Fin k) := Finset.univ.filter fun j => δ * scale n ≤ w n j
  have hs : Submodule.span ℝ (arms '' (s : Set (Fin k))) = ⊤ := by
    by_contra h
    obtain ⟨j, hjs, hj⟩ := hn s h
    apply hjs
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mul_le_mul_of_nonneg_right (hδc s) hnscale).trans hj
  intro v
  have hframe : β * (v ⬝ᵥ v) ≤ ∑ j ∈ s, (arms j ⬝ᵥ v) ^ 2 := by
    apply le_trans _ (hbound s hs v)
    exact mul_le_mul_of_nonneg_right (hβb s)
      (by simpa only [star_trivial] using dotProduct_star_self_nonneg v)
  calc
    δ * β * scale n * (v ⬝ᵥ v) = δ * scale n * (β * (v ⬝ᵥ v)) := by ring
    _ ≤ δ * scale n * (∑ j ∈ s, (arms j ⬝ᵥ v) ^ 2) :=
      mul_le_mul_of_nonneg_left hframe (mul_nonneg hδ.le hnscale)
    _ = ∑ j ∈ s, (δ * scale n) * (arms j ⬝ᵥ v) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ s, w n j * (arms j ⬝ᵥ v) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hj).2 (sq_nonneg _)
    _ ≤ ∑ j : Fin k, w n j * (arms j ⬝ᵥ v) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun j _ _ => mul_nonneg (hw n j) (sq_nonneg _))

/-- A fixed information-bearing perturbation annihilating a set of arms forces
one of the remaining arms to receive a logarithmic weight. -/
lemma missing_mass_of_information {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (w : ℕ → Fin k → ℝ)
    (scale : ℕ → ℝ) (s : Finset (Fin k)) (v : Fin d → ℝ)
    (hzero : ∀ j ∈ s, arms j ⬝ᵥ v = 0)
    (hscale : ∀ᶠ n : ℕ in atTop, 0 < scale n)
    (hinfo : ∀ᶠ n : ℕ in atTop,
      scale n ≤ ∑ j : Fin k, w n j * (arms j ⬝ᵥ v) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∃ j : Fin k, j ∉ s ∧ c * scale n ≤ w n j := by
  classical
  let M : ℝ := ∑ j : Fin k, (arms j ⬝ᵥ v) ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => sq_nonneg _
  let c : ℝ := (M + 1)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hcM : c * M < 1 := by
    dsimp [c]
    rw [inv_mul_eq_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hscale, hinfo] with n hn hi
  by_contra h
  push Not at h
  have hb : ∑ j : Fin k, w n j * (arms j ⬝ᵥ v) ^ 2 ≤ c * scale n * M := by
    rw [show c * scale n * M =
      ∑ j : Fin k, (c * scale n) * (arms j ⬝ᵥ v) ^ 2 by
        simp only [M, Finset.mul_sum]]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hjs : j ∈ s
    · simp [hzero j hjs]
    · exact mul_le_mul_of_nonneg_right (h j hjs).le (sq_nonneg _)
  have : c * scale n * M < scale n := by nlinarith [mul_lt_mul_of_pos_right hcM hn]
  linarith

lemma uniform_design_of_information {k d : ℕ}
    (arms : Fin k → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (θ : Fin d → ℝ) (star : Fin k)
    (w : ℕ → Fin k → ℝ) (scale : ℕ → ℝ)
    (hw : ∀ n j, 0 ≤ w n j)
    (hscale : ∀ᶠ n : ℕ in atTop, 0 < scale n)
    (hstar : ∀ᶠ n : ℕ in atTop, scale n ≤ w n star)
    (hinfo : ∀ u : Fin d → ℝ,
      (∃ j : Fin k, arms star ⬝ᵥ (θ + u) < arms j ⬝ᵥ (θ + u)) →
      ∀ᶠ n : ℕ in atTop,
        scale n ≤ ∑ j : Fin k, w n j * (arms j ⬝ᵥ u) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ v : Fin d → ℝ,
      c * scale n * (v ⬝ᵥ v) ≤
        ∑ j : Fin k, w n j * (arms j ⬝ᵥ v) ^ 2 := by
  classical
  apply finite_frame_eventual_lower_bound arms w scale hw (hscale.mono fun _ h => h.le)
  intro s hs
  by_cases hstars : star ∈ s
  · obtain ⟨u, hu, halt⟩ := proper_subset_alternative arms hspan θ star s hstars hs
    exact missing_mass_of_information arms w scale s u hu hscale (hinfo u halt)
  · refine ⟨1, by norm_num, hstar.mono ?_⟩
    intro n hn
    exact ⟨star, hstars, by simpa using hn⟩

lemma eventually_posDef_of_uniform_bound {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (w : ℕ → Fin k → ℝ) (scale : ℕ → ℝ)
    (hscale : ∀ᶠ n : ℕ in atTop, 0 < scale n)
    (hbound : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ v : Fin d → ℝ,
      c * scale n * (v ⬝ᵥ v) ≤
        ∑ j : Fin k, w n j * (arms j ⬝ᵥ v) ^ 2) :
    ∀ᶠ n : ℕ in atTop,
      (∑ j : Fin k, w n j • vecMulVec (arms j) (arms j)).PosDef := by
  obtain ⟨c, hc, hb⟩ := hbound
  filter_upwards [hscale, hb] with n hn hnb
  exact outer_design_posDef_of_lower_bound arms (w n) (c * scale n)
    (mul_pos hc hn) hnb


end AsymptoticLinearBandit
end

/- Component: SharpInverseDesign. -/
section
open Matrix Filter Set
open scoped Topology BigOperators

namespace SharpInverseDesign

noncomputable def design {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (w : Fin k → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ j, w j • vecMulVec (arms j) (arms j)

noncomputable def energy {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (w : Fin k → ℝ) (v : Fin d → ℝ) : ℝ :=
  ∑ j, w j * (arms j ⬝ᵥ v) ^ 2

theorem design_quadratic {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (w : Fin k → ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ design arms w *ᵥ v = energy arms w v :=
  AsymptoticLinearBandit.outer_design_quadratic arms w v

theorem energy_nonneg {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (w : Fin k → ℝ) (hw : ∀ j, 0 ≤ w j) (v : Fin d → ℝ) :
    0 ≤ energy arms w v :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)

theorem weighted_coordinate_le_energy {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (w : Fin k → ℝ) (hw : ∀ j, 0 ≤ w j) (v : Fin d → ℝ) (j : Fin k) :
    w j * (arms j ⬝ᵥ v) ^ 2 ≤ energy arms w v := by
  exact Finset.single_le_sum
    (fun i _ => mul_nonneg (hw i) (sq_nonneg (arms i ⬝ᵥ v))) (Finset.mem_univ j)

/- A finite arm set permits a relative coordinate comparison at every nonzero
limit projection. Zero limit projections vanish before the varying weights
are used, so the weights need not be bounded or convergent. -/
theorem energy_limit_le_mul {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (w : ℕ → Fin k → ℝ) (hw : ∀ n j, 0 ≤ w n j)
    (u : ℕ → Fin d → ℝ) (v : Fin d → ℝ)
    (hu : Tendsto u atTop (𝓝 v)) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ n : ℕ in atTop, energy arms (w n) v ≤ r * energy arms (w n) (u n) := by
  have hr0 : 0 ≤ r := (zero_lt_one.trans hr).le
  have hcoords : ∀ j : Fin k, ∀ᶠ n : ℕ in atTop,
      (arms j ⬝ᵥ v) ^ 2 ≤ r * (arms j ⬝ᵥ u n) ^ 2 := by
    intro j
    by_cases hz : arms j ⬝ᵥ v = 0
    · exact Eventually.of_forall fun n => by simp only [hz, zero_pow two_ne_zero]; positivity
    · have hcont : Continuous (fun z : Fin d → ℝ => arms j ⬝ᵥ z) :=
        continuous_const.dotProduct continuous_id
      have hlim := (hcont.tendsto v).comp hu
      have hlim' : Tendsto (fun n => r * (arms j ⬝ᵥ u n) ^ 2) atTop
          (𝓝 (r * (arms j ⬝ᵥ v) ^ 2)) :=
        tendsto_const_nhds.mul (hlim.pow 2)
      have hstrict : (arms j ⬝ᵥ v) ^ 2 < r * (arms j ⬝ᵥ v) ^ 2 := by
        nlinarith [mul_pos (sub_pos.mpr hr) (sq_pos_of_ne_zero hz)]
      exact Filter.Tendsto.eventually_const_le hstrict hlim'
  filter_upwards [eventually_all.2 hcoords] with n hn
  calc
    energy arms (w n) v ≤ ∑ j, w n j * (r * (arms j ⬝ᵥ u n) ^ 2) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hn j) (hw n j)
    _ = r * energy arms (w n) (u n) := by
      rw [energy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem no_bounded_alternative_sequence {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (theta : Fin d → ℝ) (star j : Fin k)
    (w : ℕ → Fin k → ℝ) (hw : ∀ n i, 0 ≤ w n i)
    (hstar : Tendsto (fun n => w n star) atTop atTop)
    (hinfo : ∀ v : Fin d → ℝ,
      (∃ i, arms star ⬝ᵥ (theta + v) < arms i ⬝ᵥ (theta + v)) →
      ∀ C < (2 : ℝ), ∀ᶠ n : ℕ in atTop, C ≤ energy arms (w n) v)
    (u : ℕ → Fin d → ℝ) (M s R : ℝ)
    (hbox : ∀ n, u n ∈ Icc (fun _ => -M) (fun _ => M))
    (hproj : ∀ n, arms j ⬝ᵥ u n = s)
    (hs : arms star ⬝ᵥ theta - arms j ⬝ᵥ theta < s)
    (hR0 : 0 < R) (hR2 : R < 2)
    (henergy : ∀ n, energy arms (w n) (u n) ≤ R) : False := by
  obtain ⟨v, hvbox, phi, hphi, huv⟩ :=
    (isCompact_Icc : IsCompact (Icc (fun _ : Fin d => -M) (fun _ => M))).tendsto_subseq hbox
  let D := (R + 2) / 2
  have hRD : R < D := by dsimp [D]; linarith
  have hD2 : D < 2 := by dsimp [D]; linarith
  let r := D / R
  have hr : 1 < r := (lt_div_iff₀ hR0).2 (by simpa using hRD)
  have hrR : r * R = D := div_mul_cancel₀ D hR0.ne'
  have htransfer := energy_limit_le_mul arms (fun n => w (phi n))
    (fun n i => hw (phi n) i) (u ∘ phi) v huv hr
  have hfixed : ∀ᶠ n : ℕ in atTop, energy arms (w (phi n)) v ≤ D := by
    filter_upwards [htransfer] with n hn
    apply hn.trans
    calc
      r * energy arms (w (phi n)) (u (phi n)) ≤ r * R :=
        mul_le_mul_of_nonneg_left (henergy (phi n)) (zero_lt_one.trans hr).le
      _ = D := hrR
  have hstarzero : arms star ⬝ᵥ v = 0 := by
    by_contra hz
    have hz2 : 0 < (arms star ⬝ᵥ v) ^ 2 := sq_pos_of_ne_zero hz
    have hlarge := (hstar.comp hphi.tendsto_atTop).eventually_gt_atTop
      (D / (arms star ⬝ᵥ v) ^ 2)
    have hfalse : ∀ᶠ n : ℕ in atTop, False := by
      filter_upwards [hfixed, hlarge] with n hn hlarge
      have hlower := weighted_coordinate_le_energy arms (w (phi n))
        (hw (phi n)) v star
      have hstrict : D < w (phi n) star * (arms star ⬝ᵥ v) ^ 2 :=
        (div_lt_iff₀ hz2).1 hlarge
      linarith
    exact hfalse.exists.elim fun _ h => h
  have hcont : Continuous (fun z : Fin d → ℝ => arms j ⬝ᵥ z) :=
    continuous_const.dotProduct continuous_id
  have hlim := (hcont.tendsto v).comp huv
  have hlim' : Tendsto (fun n => arms j ⬝ᵥ u (phi n)) atTop (𝓝 s) := by
    simpa only [hproj] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => s) atTop (𝓝 s))
  have hvj : arms j ⬝ᵥ v = s := tendsto_nhds_unique hlim hlim'
  have hbetter : arms star ⬝ᵥ (theta + v) < arms j ⬝ᵥ (theta + v) := by
    simp only [dotProduct_add, hstarzero, hvj, add_zero]
    linarith
  have hC : (D + 2) / 2 < 2 := by linarith
  have hlower := hphi.tendsto_atTop.eventually (hinfo v ⟨j, hbetter⟩ _ hC)
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hfixed, hlower] with n hn hlow
    linarith
  exact hfalse.exists.elim fun _ h => h

noncomputable def inversePerturb {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ)
    (a : Fin d → ℝ) (s : ℝ) : Fin d → ℝ :=
  (s / (a ⬝ᵥ V⁻¹ *ᵥ a)) • (V⁻¹ *ᵥ a)

theorem inversePerturb_projection {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ)
    (a : Fin d → ℝ) (s : ℝ) (hq : a ⬝ᵥ V⁻¹ *ᵥ a ≠ 0) :
    a ⬝ᵥ inversePerturb V a s = s := by
  rw [inversePerturb, dotProduct_smul]
  exact div_mul_cancel₀ s hq

theorem inversePerturb_quadratic {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ)
    (hV : V.PosDef) (a : Fin d → ℝ) (s : ℝ) (hq : a ⬝ᵥ V⁻¹ *ᵥ a ≠ 0) :
    inversePerturb V a s ⬝ᵥ V *ᵥ inversePerturb V a s =
      s ^ 2 / (a ⬝ᵥ V⁻¹ *ᵥ a) := by
  have hcancel : V *ᵥ (V⁻¹ *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv V (hV.isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]
  rw [inversePerturb, Matrix.mulVec_smul, hcancel, smul_dotProduct, dotProduct_smul,
    dotProduct_comm (V⁻¹ *ᵥ a) a]
  change (s / (a ⬝ᵥ V⁻¹ *ᵥ a)) *
      ((s / (a ⬝ᵥ V⁻¹ *ᵥ a)) * (a ⬝ᵥ V⁻¹ *ᵥ a)) = _
  field_simp [hq]

theorem coordinate_sq_le_self_dot {d : ℕ} (v : Fin d → ℝ) (i : Fin d) :
    (v i) ^ 2 ≤ v ⬝ᵥ v := by
  simpa only [dotProduct, pow_two] using
    (Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i))

theorem eventually_inverse_quadratic_le {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (theta : Fin d → ℝ) (star j : Fin k)
    (w : ℕ → Fin k → ℝ) (hw : ∀ n i, 0 ≤ w n i)
    (hstar : Tendsto (fun n => w n star) atTop atTop)
    (hinfo : ∀ v : Fin d → ℝ,
      (∃ i, arms star ⬝ᵥ (theta + v) < arms i ⬝ᵥ (theta + v)) →
      ∀ C < (2 : ℝ), ∀ᶠ n : ℕ in atTop, C ≤ energy arms (w n) v)
    {c : ℝ} (hc : 0 < c)
    (hcoerce : ∀ᶠ n : ℕ in atTop, ∀ v : Fin d → ℝ,
      c * (v ⬝ᵥ v) ≤ energy arms (w n) v)
    (hpos : ∀ᶠ n : ℕ in atTop, (design arms (w n)).PosDef)
    (hgap : 0 ≤ arms star ⬝ᵥ theta - arms j ⬝ᵥ theta)
    {B : ℝ} (hB : (arms star ⬝ᵥ theta - arms j ⬝ᵥ theta) ^ 2 / 2 < B) :
    ∀ᶠ n : ℕ in atTop,
      arms j ⬝ᵥ (design arms (w n))⁻¹ *ᵥ arms j ≤ B := by
  by_contra hevent
  have hfreq : ∃ᶠ n : ℕ in atTop,
      B < arms j ⬝ᵥ (design arms (w n))⁻¹ *ᵥ arms j := by
    simpa only [Filter.Frequently, not_lt] using hevent
  obtain ⟨phi, hphi, hphiGood⟩ :=
    extraction_of_frequently_atTop (hfreq.and_eventually (hpos.and hcoerce))
  have hB0 : 0 < B := lt_of_le_of_lt (by positivity) hB
  have hroot : arms star ⬝ᵥ theta - arms j ⬝ᵥ theta < Real.sqrt (2 * B) :=
    Real.lt_sqrt_of_sq_lt (by linarith)
  obtain ⟨s, hs, hsroot⟩ := exists_between hroot
  have hs0 : 0 < s := hgap.trans_lt hs
  have hs2 : s ^ 2 < 2 * B := by
    have h := (sq_lt_sq₀ hs0.le (Real.sqrt_nonneg (2 * B))).2 hsroot
    simpa only [Real.sq_sqrt (by positivity : 0 ≤ 2 * B)] using h
  let R := s ^ 2 / B
  have hR0 : 0 < R := div_pos (sq_pos_of_pos hs0) hB0
  have hR2 : R < 2 := (div_lt_iff₀ hB0).2 (by linarith)
  let u : ℕ → Fin d → ℝ := fun n =>
    inversePerturb (design arms (w (phi n))) (arms j) s
  have hqpos (n : ℕ) : 0 < arms j ⬝ᵥ (design arms (w (phi n)))⁻¹ *ᵥ arms j :=
    hB0.trans (hphiGood n).1
  have hproj (n : ℕ) : arms j ⬝ᵥ u n = s :=
    inversePerturb_projection _ _ _ (hqpos n).ne'
  have henergy (n : ℕ) : energy arms (w (phi n)) (u n) ≤ R := by
    rw [← design_quadratic]
    change inversePerturb _ _ _ ⬝ᵥ _ *ᵥ inversePerturb _ _ _ ≤ _
    rw [inversePerturb_quadratic _ (hphiGood n).2.1 _ _ (hqpos n).ne']
    exact div_le_div_of_nonneg_left (sq_nonneg s) hB0 (hphiGood n).1.le
  let M := Real.sqrt (2 / c)
  have hbox : ∀ n, u n ∈ Icc (fun _ => -M) (fun _ => M) := by
    intro n
    have hb (i : Fin d) : |u n i| ≤ M := by
      have hcoord := coordinate_sq_le_self_dot (u n) i
      have hco := (hphiGood n).2.2 (u n)
      have hsmall : c * (u n i) ^ 2 ≤ 2 := by
        have hscaled := mul_le_mul_of_nonneg_left hcoord hc.le
        linarith [henergy n]
      apply Real.abs_le_sqrt
      exact (le_div_iff₀ hc).2 (by nlinarith)
    exact ⟨fun i => (abs_le.1 (hb i)).1, fun i => (abs_le.1 (hb i)).2⟩
  apply no_bounded_alternative_sequence arms theta star j (fun n => w (phi n))
    (fun n i => hw (phi n) i) (hstar.comp hphi.tendsto_atTop) _ u M s R hbox hproj hs hR0 hR2 henergy
  intro v hv C hC
  exact hphi.tendsto_atTop.eventually (hinfo v hv C hC)


end SharpInverseDesign
end

/- Component: AllocationLiminf. -/
section
open Matrix MeasureTheory ProbabilityTheory Filter ENNReal
open scoped BigOperators

namespace BanditAlgorithm.AsymptoticAllocation

lemma gap_nonneg {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (θ : Fin d → ℝ) (j : Fin k) : 0 ≤ linearArmGap arms θ j := by
  unfold linearArmGap
  exact sub_nonneg.mpr
    (le_ciSup (Set.finite_range (fun i : Fin k ↦ arms i ⬝ᵥ θ)).bddAbove j)

lemma matrix_scale {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (w : Fin k → ℝ) (s : ℝ) :
    linearAllocationMatrix arms (fun j ↦ s * w j) =
      s • linearAllocationMatrix arms w := by
  simp only [linearAllocationMatrix, Finset.smul_sum, smul_smul]

lemma inverse_scale {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ)
    (hG : G.PosDef) (s : ℝ) (hs : s ≠ 0) :
    (s • G)⁻¹ = s⁻¹ • G⁻¹ := by
  letI := invertibleOfNonzero hs
  simpa only [invOf_eq_inv] using
    Matrix.inv_smul G s (G.isUnit_iff_isUnit_det.mp hG.isUnit)

lemma value_le_feasible {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (θ : Fin d → ℝ) (α : Fin k → ℝ)
    (hα : ∀ j, 0 ≤ α j) (hPD : (linearAllocationMatrix arms α).PosDef)
    (hconstraint : ∀ j, 0 < linearArmGap arms θ j →
      arms j ⬝ᵥ (linearAllocationMatrix arms α)⁻¹ *ᵥ arms j ≤
        linearArmGap arms θ j ^ 2 / 2) :
    linearBanditAllocationValue arms θ ≤ ∑ j, α j * linearArmGap arms θ j := by
  unfold linearBanditAllocationValue
  refine csInf_le ?_ ⟨α, ⟨hα, hPD, hconstraint⟩, rfl⟩
  refine ⟨0, ?_⟩
  rintro _ ⟨β, hβ, rfl⟩
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hβ.1 j) (gap_nonneg arms θ j)

lemma eventually_inflated_constraints {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (θ : Fin d → ℝ)
    (G : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hlim : ∀ j : Fin k,
      atTop.limsup (fun n : ℕ ↦ ENNReal.ofReal
        (Real.log n * (arms j ⬝ᵥ (G n)⁻¹ *ᵥ arms j))) ≤
      ENNReal.ofReal (linearArmGap arms θ j ^ 2 / 2))
    (r : ℝ) (hr : 1 < r) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Fin k, 0 < linearArmGap arms θ j →
      Real.log n * (arms j ⬝ᵥ (G n)⁻¹ *ᵥ arms j) ≤
        r * (linearArmGap arms θ j ^ 2 / 2) := by
  apply Filter.eventually_all.mpr
  intro j
  by_cases hj : 0 < linearArmGap arms θ j
  · have hgap : 0 < linearArmGap arms θ j ^ 2 / 2 := by positivity
    have hr0 : 0 < r := lt_trans zero_lt_one hr
    have hstrict : ENNReal.ofReal (linearArmGap arms θ j ^ 2 / 2) <
        ENNReal.ofReal (r * (linearArmGap arms θ j ^ 2 / 2)) := by
      rw [ENNReal.ofReal_lt_ofReal_iff (mul_pos hr0 hgap)]
      nlinarith
    filter_upwards [Filter.eventually_lt_of_limsup_lt ((hlim j).trans_lt hstrict)]
      with n hn
    intro _
    exact ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hr0 hgap)).mp hn).le
  · exact Filter.Eventually.of_forall fun _ h ↦ (hj h).elim

lemma eventually_value_le_scaled_cost {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (θ : Fin d → ℝ)
    (w : ℕ → Fin k → ℝ) (hw : ∀ n j, 0 ≤ w n j)
    (hPD : ∀ᶠ n : ℕ in atTop, (linearAllocationMatrix arms (w n)).PosDef)
    (hlim : ∀ j : Fin k,
      atTop.limsup (fun n : ℕ ↦ ENNReal.ofReal (Real.log n *
        (arms j ⬝ᵥ (linearAllocationMatrix arms (w n))⁻¹ *ᵥ arms j))) ≤
      ENNReal.ofReal (linearArmGap arms θ j ^ 2 / 2))
    (r : ℝ) (hr : 1 < r) :
    ∀ᶠ n : ℕ in atTop,
      linearBanditAllocationValue arms θ ≤
        r * ((∑ j, w n j * linearArmGap arms θ j) / Real.log n) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  filter_upwards [hPD, eventually_inflated_constraints arms θ _ hlim r hr,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hnPD hnC hn
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  let α : Fin k → ℝ := fun j ↦ (r / Real.log n) * w n j
  have hα : ∀ j, 0 ≤ α j := fun j ↦ mul_nonneg (div_pos hr0 hnlog).le (hw n j)
  have hmatrix : linearAllocationMatrix arms α =
      (r / Real.log n) • linearAllocationMatrix arms (w n) :=
    matrix_scale arms (w n) _
  have hαPD : (linearAllocationMatrix arms α).PosDef := by
    rw [hmatrix]
    exact hnPD.smul (div_pos hr0 hnlog)
  have hαC : ∀ j, 0 < linearArmGap arms θ j →
      arms j ⬝ᵥ (linearAllocationMatrix arms α)⁻¹ *ᵥ arms j ≤
        linearArmGap arms θ j ^ 2 / 2 := by
    intro j hj
    rw [hmatrix, inverse_scale _ hnPD _ (div_pos hr0 hnlog).ne',
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hbound := hnC j hj
    have hid : (r / Real.log n)⁻¹ *
        (arms j ⬝ᵥ (linearAllocationMatrix arms (w n))⁻¹ *ᵥ arms j) =
        (Real.log n *
          (arms j ⬝ᵥ (linearAllocationMatrix arms (w n))⁻¹ *ᵥ arms j)) / r := by
      simp only [inv_div]
      ring
    rw [hid]
    exact (div_le_iff₀ hr0).mpr (by nlinarith [hbound])
  have hcost := value_le_feasible arms θ α hα hαPD hαC
  have hcosteq : (∑ j, α j * linearArmGap arms θ j) =
      r * ((∑ j, w n j * linearArmGap arms θ j) / Real.log n) := by
    simp only [α, mul_assoc, ← Finset.mul_sum]
    ring
  rwa [hcosteq] at hcost

lemma ofReal_le_liminf_of_eventually_scaled {c : ℝ} {f : ℕ → ℝ}
    (h : ∀ r : ℝ, 1 < r → ∀ᶠ n : ℕ in atTop, c ≤ r * f n) :
    ENNReal.ofReal c ≤ atTop.liminf (fun n : ℕ ↦ ENNReal.ofReal (f n)) := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro t ht htc
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast ht
  have htc' : (t : ℝ) < c := ENNReal.coe_lt_ofReal.mp htc
  let r : ℝ := (c / t + 1) / 2
  have hr : 1 < r := by
    have hct : 1 < c / (t : ℝ) := (lt_div_iff₀ ht0).mpr (by simpa using htc')
    dsimp [r]
    linarith
  have hrt : r * (t : ℝ) < c := by
    dsimp [r]
    field_simp
    nlinarith
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [h r hr] with n hn
  have htf : (t : ℝ) ≤ f n := by nlinarith [lt_trans zero_lt_one hr]
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal htf

theorem allocation_liminf_of_design_limits {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (θ : Fin d → ℝ)
    (w : ℕ → Fin k → ℝ) (hw : ∀ n j, 0 ≤ w n j)
    (hPD : ∀ᶠ n : ℕ in atTop, (linearAllocationMatrix arms (w n)).PosDef)
    (hlim : ∀ j : Fin k,
      atTop.limsup (fun n : ℕ ↦ ENNReal.ofReal (Real.log n *
        (arms j ⬝ᵥ (linearAllocationMatrix arms (w n))⁻¹ *ᵥ arms j))) ≤
      ENNReal.ofReal (linearArmGap arms θ j ^ 2 / 2)) :
    ENNReal.ofReal (linearBanditAllocationValue arms θ) ≤
      atTop.liminf (fun n : ℕ ↦ ENNReal.ofReal
        ((∑ j, w n j * linearArmGap arms θ j) / Real.log n)) := by
  apply ofReal_le_liminf_of_eventually_scaled
  exact eventually_value_le_scaled_cost arms θ w hw hPD hlim

end BanditAlgorithm.AsymptoticAllocation
end

/- Component: LinearDesignLimits. -/
section
open Matrix Filter MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped BigOperators Topology

namespace AsymptoticLinearBandit

lemma log_le_half {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div hx.ne' (by norm_num)] at h
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem uniform_log_nondegeneracy {k d : ℕ}
    (arms : Fin k → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (pi : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {nu : StochasticBandit k | ∃ theta' : Fin d → ℝ, nu = gaussianLinearBandit arms theta'} pi)
    (theta : Fin d → ℝ) (jstar : Fin k)
    (hopt : ∀ j, j ≠ jstar → arms j ⬝ᵥ theta < arms jstar ⬝ᵥ theta) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ v : Fin d → ℝ,
      c * Real.log n * (v ⬝ᵥ v) ≤
        v ⬝ᵥ linearBanditExpectedDesign arms (gaussianLinearBandit arms theta) pi n *ᵥ v := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < n)
  have hstar : ∀ᶠ n : ℕ in atTop, Real.log n ≤
      expectedPulls (gaussianLinearBandit arms theta) pi n jstar := by
    filter_upwards [optimal_expected_pulls_ge_half_eventually arms pi hcons theta jstar hopt,
      eventually_ge_atTop (1 : ℕ)] with n hn hnpos
    exact (log_le_half (by exact_mod_cast (by omega : 0 < n))).trans hn
  obtain ⟨c, hc, hb⟩ := uniform_design_of_information arms hspan theta jstar
    (fun n => expectedPulls (gaussianLinearBandit arms theta) pi n)
    (fun n => Real.log n) (fun n j => expected_pull_nonneg _ pi n j) hlog hstar
    (fun u halt => by
      simpa using information_quadratic_eventually arms pi hcons theta jstar hopt
        u halt (1 / 2) (by norm_num))
  refine ⟨c, hc, hb.mono ?_⟩
  intro n hn v
  rw [design_quadratic_eq_sum]
  exact hn v

theorem expected_design_eventually_posDef {k d : ℕ}
    (arms : Fin k → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (pi : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {nu : StochasticBandit k | ∃ theta' : Fin d → ℝ, nu = gaussianLinearBandit arms theta'} pi)
    (theta : Fin d → ℝ) (jstar : Fin k)
    (hopt : ∀ j, j ≠ jstar → arms j ⬝ᵥ theta < arms jstar ⬝ᵥ theta) :
    ∀ᶠ n : ℕ in atTop,
      (linearBanditExpectedDesign arms (gaussianLinearBandit arms theta) pi n).PosDef := by
  obtain ⟨c, hc, hb⟩ := uniform_log_nondegeneracy arms hspan pi hcons theta jstar hopt
  filter_upwards [hb, eventually_ge_atTop (2 : ℕ)] with n hn hnlarge
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  apply outer_design_posDef_of_lower_bound arms
    (expectedPulls (gaussianLinearBandit arms theta) pi n) (c * Real.log n)
    (mul_pos hc hnlog)
  intro v
  simpa only [design_quadratic_eq_sum] using hn v

noncomputable def normalizedExpectedPulls {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (theta : Fin d → ℝ)
    (pi : BanditPolicy k) (n : ℕ) (j : Fin k) : ℝ :=
  expectedPulls (gaussianLinearBandit arms theta) pi n j / Real.log n

lemma normalizedExpectedPulls_nonneg {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (theta : Fin d → ℝ)
    (pi : BanditPolicy k) (n : ℕ) (j : Fin k) :
    0 ≤ normalizedExpectedPulls arms theta pi n j :=
  div_nonneg (expected_pull_nonneg _ pi n j) (Real.log_natCast_nonneg n)

lemma normalized_energy {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (theta : Fin d → ℝ)
    (pi : BanditPolicy k) (n : ℕ) (v : Fin d → ℝ) :
    (∑ j, normalizedExpectedPulls arms theta pi n j * (arms j ⬝ᵥ v) ^ 2) =
      (∑ j, expectedPulls (gaussianLinearBandit arms theta) pi n j *
        (arms j ⬝ᵥ v) ^ 2) / Real.log n := by
  simp only [normalizedExpectedPulls, Finset.sum_div, div_mul_eq_mul_div]

lemma nat_div_log_tendsto_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) / Real.log n) atTop atTop := by
  have hzero : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log n / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
      (by exact_mod_cast (by omega : 0 < n))
  simpa only [Function.comp_def, inv_div] using
    (tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩))

theorem normalized_optimal_pulls_tendsto_atTop {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (pi : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {nu : StochasticBandit k | ∃ theta' : Fin d → ℝ, nu = gaussianLinearBandit arms theta'} pi)
    (theta : Fin d → ℝ) (jstar : Fin k)
    (hopt : ∀ j, j ≠ jstar → arms j ⬝ᵥ theta < arms jstar ⬝ᵥ theta) :
    Tendsto (fun n => normalizedExpectedPulls arms theta pi n jstar) atTop atTop := by
  apply tendsto_atTop_mono' atTop _
    (nat_div_log_tendsto_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [optimal_expected_pulls_ge_half_eventually arms pi hcons theta jstar hopt]
    with n hn
  dsimp [normalizedExpectedPulls]
  have hb := div_le_div_of_nonneg_right hn (Real.log_natCast_nonneg n)
  convert hb using 1
  ring


end AsymptoticLinearBandit
end

/- Component: InverseDesignLimits. -/
section
open Matrix Filter MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped BigOperators Topology

namespace AsymptoticLinearBandit

lemma gap_eq_optimal_difference {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (star : Fin k)
    (hopt : ∀ j, j ≠ star → arms j ⬝ᵥ theta < arms star ⬝ᵥ theta) (j : Fin k) :
    linearArmGap arms theta j = arms star ⬝ᵥ theta - arms j ⬝ᵥ theta := by
  letI : Nonempty (Fin k) := ⟨star⟩
  have hmax : (⨆ i, arms i ⬝ᵥ theta) = arms star ⬝ᵥ theta := by
    apply le_antisymm
    · apply ciSup_le
      intro i
      by_cases hi : i = star
      · simp [hi]
      · exact (hopt i hi).le
    · exact le_ciSup (Set.finite_range (fun i => arms i ⬝ᵥ theta)).bddAbove star
  simp [linearArmGap, hmax]

lemma normalized_design_scale {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (theta : Fin d → ℝ) (pi : BanditPolicy k) (n : ℕ) :
    SharpInverseDesign.design arms (normalizedExpectedPulls arms theta pi n) =
      (Real.log n)⁻¹ •
        linearBanditExpectedDesign arms (gaussianLinearBandit arms theta) pi n := by
  simp only [SharpInverseDesign.design, normalizedExpectedPulls,
    linearBanditExpectedDesign, expectedPulls, Finset.smul_sum, smul_smul,
    div_eq_mul_inv, mul_comm]

lemma normalized_uniform_coercivity {k d : ℕ}
    (arms : Fin k → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (pi : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {nu : StochasticBandit k | ∃ theta' : Fin d → ℝ, nu = gaussianLinearBandit arms theta'} pi)
    (theta : Fin d → ℝ) (star : Fin k)
    (hopt : ∀ j, j ≠ star → arms j ⬝ᵥ theta < arms star ⬝ᵥ theta) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ v : Fin d → ℝ,
      c * (v ⬝ᵥ v) ≤
        SharpInverseDesign.energy arms (normalizedExpectedPulls arms theta pi n) v := by
  obtain ⟨c, hc, hb⟩ := uniform_log_nondegeneracy arms hspan pi hcons theta star hopt
  refine ⟨c, hc, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (2 : ℕ)] with n hn hnlarge
  intro v
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [SharpInverseDesign.energy, normalized_energy]
  apply (le_div_iff₀ hnlog).mpr
  have hv := hn v
  rw [design_quadratic_eq_sum] at hv
  nlinarith

lemma normalized_information_eventually {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (pi : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {nu : StochasticBandit k | ∃ theta' : Fin d → ℝ, nu = gaussianLinearBandit arms theta'} pi)
    (theta : Fin d → ℝ) (star : Fin k)
    (hopt : ∀ j, j ≠ star → arms j ⬝ᵥ theta < arms star ⬝ᵥ theta)
    (v : Fin d → ℝ)
    (halt : ∃ j, arms star ⬝ᵥ (theta + v) < arms j ⬝ᵥ (theta + v))
    (C : ℝ) (hC : C < 2) :
    ∀ᶠ n : ℕ in atTop, C ≤
      SharpInverseDesign.energy arms (normalizedExpectedPulls arms theta pi n) v := by
  filter_upwards [information_quadratic_eventually arms pi hcons theta star hopt
    v halt (C / 2) (by linarith), eventually_ge_atTop (2 : ℕ)] with n hn hnlarge
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [SharpInverseDesign.energy, normalized_energy]
  exact (le_div_iff₀ hnlog).mpr (by nlinarith [hn])

theorem inverse_log_bound_eventually {k d : ℕ}
    (arms : Fin k → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (pi : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {nu : StochasticBandit k | ∃ theta' : Fin d → ℝ, nu = gaussianLinearBandit arms theta'} pi)
    (theta : Fin d → ℝ) (star : Fin k)
    (hopt : ∀ j, j ≠ star → arms j ⬝ᵥ theta < arms star ⬝ᵥ theta)
    (j : Fin k) (B : ℝ) (hB : linearArmGap arms theta j ^ 2 / 2 < B) :
    ∀ᶠ n : ℕ in atTop,
      Real.log n * (arms j ⬝ᵥ
        (linearBanditExpectedDesign arms (gaussianLinearBandit arms theta) pi n)⁻¹ *ᵥ
          arms j) ≤ B := by
  obtain ⟨c, hc, hcoerce⟩ := normalized_uniform_coercivity arms hspan pi hcons theta star hopt
  have hpos : ∀ᶠ n : ℕ in atTop,
      (SharpInverseDesign.design arms (normalizedExpectedPulls arms theta pi n)).PosDef := by
    filter_upwards [hcoerce] with n hn
    exact outer_design_posDef_of_lower_bound arms _ c hc hn
  have hgap := linear_gap_nonneg arms theta j
  rw [gap_eq_optimal_difference arms theta star hopt j] at hB hgap
  have hbound := SharpInverseDesign.eventually_inverse_quadratic_le arms theta star j
    (normalizedExpectedPulls arms theta pi)
    (normalizedExpectedPulls_nonneg arms theta pi)
    (normalized_optimal_pulls_tendsto_atTop arms pi hcons theta star hopt)
    (normalized_information_eventually arms pi hcons theta star hopt)
    hc hcoerce hpos hgap hB
  filter_upwards [hbound, expected_design_eventually_posDef arms hspan pi hcons theta star hopt,
    eventually_ge_atTop (2 : ℕ)] with n hn hnPD hnlarge
  have hnlog : Real.log n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  rw [normalized_design_scale,
    AsymptoticAllocation.inverse_scale _ hnPD _ (inv_ne_zero hnlog), inv_inv,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hn
  exact hn

theorem inverse_log_limsup {k d : ℕ}
    (arms : Fin k → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (pi : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {nu : StochasticBandit k | ∃ theta' : Fin d → ℝ, nu = gaussianLinearBandit arms theta'} pi)
    (theta : Fin d → ℝ) (star : Fin k)
    (hopt : ∀ j, j ≠ star → arms j ⬝ᵥ theta < arms star ⬝ᵥ theta)
    (j : Fin k) :
    atTop.limsup (fun n : ℕ => ENNReal.ofReal (Real.log n *
      (arms j ⬝ᵥ
        (linearBanditExpectedDesign arms (gaussianLinearBandit arms theta) pi n)⁻¹ *ᵥ
          arms j))) ≤ ENNReal.ofReal (linearArmGap arms theta j ^ 2 / 2) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro eps heps _
  have hepsreal : (0 : ℝ) < eps := heps
  have hb := inverse_log_bound_eventually arms hspan pi hcons theta star hopt j
    (linearArmGap arms theta j ^ 2 / 2 + eps) (by linarith)
  have hlim := Filter.limsup_le_of_le (by isBoundedDefault)
    (hb.mono fun n hn => ENNReal.ofReal_le_ofReal hn)
  rw [ENNReal.ofReal_add (by positivity : 0 ≤ linearArmGap arms theta j ^ 2 / 2)
      eps.coe_nonneg, ENNReal.ofReal_coe_nnreal] at hlim
  exact hlim


end AsymptoticLinearBandit
end

/- Component: AsymptoticLinearBanditLowerBound. -/
section
open Matrix MeasureTheory ProbabilityTheory Filter ENNReal BanditAlgorithm

theorem solution {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (_hinj : Function.Injective arms)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (π : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {ν : StochasticBandit k | ∃ θ' : Fin d → ℝ, ν = gaussianLinearBandit arms θ'} π)
    (θ : Fin d → ℝ) (jstar : Fin k)
    (hopt : ∀ j : Fin k, j ≠ jstar → arms j ⬝ᵥ θ < arms jstar ⬝ᵥ θ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ v : Fin d → ℝ,
        c * Real.log n * (v ⬝ᵥ v) ≤
          v ⬝ᵥ linearBanditExpectedDesign arms (gaussianLinearBandit arms θ) π n *ᵥ v) ∧
    (∀ j : Fin k,
      atTop.limsup (fun n : ℕ ↦ ENNReal.ofReal (Real.log n *
          (arms j ⬝ᵥ
            (linearBanditExpectedDesign arms (gaussianLinearBandit arms θ) π n)⁻¹ *ᵥ
            arms j))) ≤
        ENNReal.ofReal (linearArmGap arms θ j ^ 2 / 2)) ∧
    ENNReal.ofReal (linearBanditAllocationValue arms θ) ≤
      atTop.liminf (fun n : ℕ ↦
          ENNReal.ofReal (banditRegret (gaussianLinearBandit arms θ) π n / Real.log n)) := by
  have hfirst := AsymptoticLinearBandit.uniform_log_nondegeneracy arms hspan π hcons θ jstar hopt
  have hsecond := AsymptoticLinearBandit.inverse_log_limsup arms hspan π hcons θ jstar hopt
  refine ⟨hfirst, hsecond, ?_⟩
  have hPD := AsymptoticLinearBandit.expected_design_eventually_posDef arms hspan π hcons θ jstar hopt
  have hthird := BanditAlgorithm.AsymptoticAllocation.allocation_liminf_of_design_limits arms θ
    (fun n => AsymptoticLinearBandit.expectedPulls (gaussianLinearBandit arms θ) π n)
    (fun n j => AsymptoticLinearBandit.expected_pull_nonneg _ π n j) hPD hsecond
  simpa only [← AsymptoticLinearBandit.regret_eq_expected_gap_sum] using hthird
end

#print axioms solution
