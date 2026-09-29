-- Prove2me | solution 1 for BanditAlgorithm.gaussian_exact_rank_reciprocal_tail_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T01:56:51.665865+00:00
-- url     : https://prove2.me/submissions/e85bd666-e58b-44e0-85c8-0b796e5a8b9c

import Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_exp_score_lintegral_le_one
import Theorems.Thm_BanditAlgorithm_gaussian_reciprocal_tail_split_envelope
import Theorems.Thm_BanditAlgorithm_armStoppedCenteredSum_eq_firstRewardsMean
import Theorems.Thm_BanditAlgorithm_gaussianBandit_isSubgaussian_one
import Definitions.Def_ThompsonSampling
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private theorem measurable_armPullCount_cast_fix
    {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    funext h
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
        Finset.univ).symm]
  apply Finset.measurable_sum
  intro t ht
  have ha : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage ha)
    measurable_const measurable_const

private theorem measurable_armStoppedCenteredSum_fix
    {k : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (u m : ℕ) :
    Measurable (armStoppedCenteredSum ν i u m) := by
  induction m with
  | zero => simp [armStoppedCenteredSum]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hcount : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            (armPullCount i (Fin.init h) : ℝ)) :=
        (measurable_armPullCount_cast_fix i).comp hinit
      have hlt : MeasurableSet
          {h : BanditHistory k (m + 1) |
            armPullCount i (Fin.init h) < u} := by
        simpa only [Nat.cast_lt] using
          measurableSet_lt hcount
            (measurable_const : Measurable
              (fun _ : BanditHistory k (m + 1) ↦ (u : ℝ)))
      have heq : MeasurableSet
          {h : BanditHistory k (m + 1) |
            (h (Fin.last m)).1 = i} :=
        (measurableSet_singleton i).preimage hlast.fst
      change Measurable (fun h : BanditHistory k (m + 1) ↦
        armStoppedCenteredSum ν i u m (Fin.init h) +
          if armPullCount i (Fin.init h) < u ∧
              (h (Fin.last m)).1 = i then
            (h (Fin.last m)).2 - banditArmMean ν i else 0)
      exact (ih.comp hinit).add
        (Measurable.ite (hlt.inter heq)
          (hlast.snd.sub measurable_const) measurable_const)

private theorem posterior_tail_standardize
    (m μ ε : ℝ) (s : ℕ) (hs : 0 < s) :
    (gaussianReal m ((s : NNReal))⁻¹).real (Set.Ioi (μ - ε)) =
      (gaussianReal 0 1).real
        (Set.Ioi ((μ - ε - m) * Real.sqrt s)) := by
  let r : ℝ := Real.sqrt s
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hmap1 :
      (gaussianReal m ((s : NNReal))⁻¹).map (fun x ↦ x - m) =
        gaussianReal 0 ((s : NNReal))⁻¹ := by
    simpa using
      (gaussianReal_map_sub_const
        (μ := m) (v := ((s : NNReal))⁻¹) m)
  have hvar :
      NNReal.mk (r ^ 2) (sq_nonneg r) * ((s : NNReal))⁻¹ = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_inv, NNReal.coe_natCast,
      NNReal.coe_one]
    have hrsq : r ^ 2 = s := by
      dsimp [r]
      rw [Real.sq_sqrt]
      positivity
    rw [hrsq]
    field_simp
  have hmap2 :
      (gaussianReal 0 ((s : NNReal))⁻¹).map (fun x ↦ r * x) =
        gaussianReal 0 1 := by
    simpa [hvar] using
      (gaussianReal_map_const_mul
        (μ := (0 : ℝ)) (v := ((s : NNReal))⁻¹) r)
  have hmap :
      (gaussianReal m ((s : NNReal))⁻¹).map
          (fun x ↦ r * (x - m)) =
        gaussianReal 0 1 := by
    rw [show (fun x : ℝ ↦ r * (x - m)) =
        (fun x ↦ r * x) ∘ (fun x ↦ x - m) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), hmap1, hmap2]
  have happ := congrArg
    (fun P : Measure ℝ ↦ P.real
      (Set.Ioi ((μ - ε - m) * r))) hmap
  change
    ((gaussianReal m ((s : NNReal))⁻¹).map
      (fun x ↦ r * (x - m))).real
        (Set.Ioi ((μ - ε - m) * r)) =
      (gaussianReal 0 1).real
        (Set.Ioi ((μ - ε - m) * r)) at happ
  rw [MeasureTheory.map_measureReal_apply (by fun_prop) measurableSet_Ioi] at happ
  have hpre :
      (fun x : ℝ ↦ r * (x - m)) ⁻¹'
          Set.Ioi ((μ - ε - m) * r) =
        Set.Ioi (μ - ε) := by
    ext x
    change (μ - ε - m) * r < r * (x - m) ↔ μ - ε < x
    constructor <;> intro h
    · nlinarith
    · nlinarith
  simpa [r, hpre] using happ

private theorem laplace_first_moment
    (a : ℝ) (ha : 0 < a) :
    (∫⁻ l : ℝ in Set.Ioi 0,
        ENNReal.ofReal (l * Real.exp (-(a * l)))) =
      ENNReal.ofReal (1 / a ^ 2) := by
  have hint : IntegrableOn
      (fun l : ℝ ↦ l * Real.exp (-(a * l))) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (by norm_num) (by norm_num) ha
    simpa only [Real.rpow_one, neg_mul] using h
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun l : ℝ ↦ l * Real.exp (-(a * l))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
    exact mul_nonneg hl.le (Real.exp_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := a) (by norm_num) ha
  have hi' :
      (∫ l : ℝ in Set.Ioi 0, l * Real.exp (-(a * l))) =
        (1 / a) ^ (2 : ℝ) * Real.Gamma 2 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one] using hi
  rw [hi', Real.rpow_two,
    show Real.Gamma 2 = 1 by
      simpa using (Real.Gamma_nat_eq_factorial 1)]
  ring

private theorem measurable_exact_rank_event
    {k n : ℕ} (i : Fin k) (s : ℕ) :
    MeasurableSet {h : BanditHistory k n | s < armPullCount i h} := by
  simpa only [Nat.cast_lt] using
    measurableSet_lt
      (measurable_const :
        Measurable (fun _ : BanditHistory k n ↦ (s : ℝ)))
      (measurable_armPullCount_cast_fix i)

theorem gaussian_exact_rank_reciprocal_tail_exponential_bound_proof :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        ∀ (i : Fin k) (s : ℕ), 0 < s →
        ∀ ε : ℝ, 0 < ε →
        ∀ n : ℕ,
          (∫⁻ h,
              if s < armPullCount i h then
                ENNReal.ofReal
                  (1 / gaussianTSTailProb i s
                    (banditArmMean (gaussianBandit μvec) i - ε) h - 1)
              else 0
              ∂banditMeasure (gaussianBandit μvec) π n) ≤
            ENNReal.ofReal
              (2 * Real.exp (-((s : ℝ) * ε ^ 2) / 8) +
                2 * C / ((s : ℝ) * ε ^ 2) *
                  Real.exp (-(3 * (s : ℝ) * ε ^ 2) / 32)) := by
  obtain ⟨C, hC, henv⟩ :=
    gaussian_reciprocal_tail_split_envelope
  refine ⟨C, hC, ?_⟩
  intro k _ μvec π i s hs ε hε n
  let ν := gaussianBandit μvec
  let μ : ℝ := banditArmMean ν i
  let r : ℝ := Real.sqrt s
  let a : ℝ := ε * r
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrsq : r ^ 2 = s := by
    dsimp [r]
    rw [Real.sq_sqrt]
    positivity
  have ha : 0 < a := mul_pos hε hr
  let E : Set (BanditHistory k n) :=
    {h | s < armPullCount i h}
  have hE : MeasurableSet E :=
    measurable_exact_rank_event i s
  let S : BanditHistory k n → ℝ :=
    armStoppedCenteredSum ν i s n
  have hS : Measurable S :=
    measurable_armStoppedCenteredSum_fix ν i s n
  let U : BanditHistory k n → ℝ := fun h ↦
    (μ - ε - armFirstRewardsMean i s h) * r
  let F : BanditHistory k n → ℝ → ENNReal := fun h l ↦
    if h ∈ E ∧ -a / 2 < U h then
      ENNReal.ofReal
        (l * Real.exp
          (l * U h - l ^ 2 / 2))
    else 0
  have hmean : Measurable
      (fun h : BanditHistory k n ↦ armFirstRewardsMean i s h) := by
    -- The finite reward-stack mean is a finite sum of measurable coordinates.
    rw [show
      (fun h : BanditHistory k n ↦ armFirstRewardsMean i s h) =
        fun h ↦
          (∑ t : Fin n,
            if (h t).1 = i ∧ armPullCountBefore i t h < s
            then (h t).2 else 0) / s by
      funext h
      unfold armFirstRewardsMean
      simp [Finset.sum_filter]]
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro t ht
    apply Measurable.ite
    · change MeasurableSet
        {h : BanditHistory k n |
          (h t).1 = i ∧ armPullCountBefore i t h < s}
      have hbefore : Measurable
          (fun h : BanditHistory k n ↦
            armPullCountBefore i t h) := by
        simp_rw [show ∀ h : BanditHistory k n,
            armPullCountBefore i t h =
              ∑ u : Fin n,
                if u < t ∧ (h u).1 = i then 1 else 0 by
          intro h
          unfold armPullCountBefore
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          ]
        apply Finset.measurable_sum
        intro u hu
        apply Measurable.ite
        · change MeasurableSet
            {h : BanditHistory k n | u < t ∧ (h u).1 = i}
          by_cases hut : u < t
          · have heq :
                {h : BanditHistory k n | u < t ∧ (h u).1 = i} =
                  (fun h : BanditHistory k n ↦ (h u).1) ⁻¹' {i} := by
              ext h
              simp [hut]
            rw [heq]
            exact (measurableSet_singleton i).preimage
              (measurable_fst.comp
                (measurable_pi_apply u :
                  Measurable (fun h : BanditHistory k n ↦ h u)))
          · simp [hut]
        · exact measurable_const
        · exact measurable_const
      exact MeasurableSet.inter
        ((measurableSet_singleton i).preimage
          (measurable_fst.comp (measurable_pi_apply t)))
        (measurableSet_lt hbefore measurable_const)
    · exact measurable_snd.comp (measurable_pi_apply t)
    · exact measurable_const
  have hU : Measurable U := by
    dsimp [U]
    fun_prop
  have hF : Measurable (Function.uncurry F) := by
    apply Measurable.ite
    · exact MeasurableSet.inter
        (hE.preimage measurable_fst)
        (measurableSet_lt measurable_const
          (hU.comp measurable_fst))
    · apply Measurable.ennreal_ofReal
      fun_prop
    · exact measurable_const
  have htail (h : BanditHistory k n) (hh : h ∈ E) :
      gaussianTSTailProb i s (μ - ε) h =
        (gaussianReal 0 1).real
          (Set.Ioi ((μ - ε - armFirstRewardsMean i s h) * r)) := by
    unfold gaussianTSTailProb
    rw [if_neg (Nat.ne_of_gt hs)]
    exact posterior_tail_standardize
      (armFirstRewardsMean i s h) μ ε s hs
  have hpoint (h : BanditHistory k n) :
      (if s < armPullCount i h then
          ENNReal.ofReal
            (1 / gaussianTSTailProb i s (μ - ε) h - 1)
        else 0) ≤
        ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 8)) +
          ENNReal.ofReal C * (∫⁻ l : ℝ in Set.Ioi 0, F h l) := by
    by_cases hh : h ∈ E
    · have hh' : s < armPullCount i h := by
        exact hh
      rw [if_pos hh']
      rw [htail h hh]
      have henvh := henv a ha (U h)
      by_cases hb : U h ≤ -a / 2
      · rw [if_pos hb] at henvh
        calc
          _ ≤ ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 8)) := by
            simpa [U] using henvh
          _ ≤ ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 8)) +
              ENNReal.ofReal C * (∫⁻ l : ℝ in Set.Ioi 0, F h l) :=
            le_add_right (le_refl _)
      · rw [if_neg hb] at henvh
        have hb' : -a / 2 < U h := lt_of_not_ge hb
        calc
          _ ≤ ENNReal.ofReal C *
              (∫⁻ l : ℝ in Set.Ioi 0,
                ENNReal.ofReal (l * Real.exp (l * U h - l ^ 2 / 2))) := by
            simpa [U] using henvh
          _ = ENNReal.ofReal C *
              (∫⁻ l : ℝ in Set.Ioi 0, F h l) := by
            congr 1
            apply lintegral_congr
            intro l
            simp [F, hh, hb']
          _ ≤ ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 8)) +
              ENNReal.ofReal C * (∫⁻ l : ℝ in Set.Ioi 0, F h l) :=
            le_add_left (le_refl _)
    · have hh' : ¬s < armPullCount i h := by
        exact hh
      rw [if_neg hh']
      exact bot_le
  calc
    (∫⁻ h,
        if s < armPullCount i h then
          ENNReal.ofReal
            (1 / gaussianTSTailProb i s (μ - ε) h - 1)
        else 0
        ∂banditMeasure ν π n) ≤
      ∫⁻ h, ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 8)) +
        ENNReal.ofReal C * (∫⁻ l : ℝ in Set.Ioi 0, F h l)
        ∂banditMeasure ν π n := lintegral_mono hpoint
    _ = ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 8)) +
        ENNReal.ofReal C *
        (∫⁻ h, (∫⁻ l : ℝ in Set.Ioi 0, F h l)
          ∂banditMeasure ν π n) := by
      rw [lintegral_add_left measurable_const]
      simp only [lintegral_const, measure_univ, mul_one]
      congr 1
      rw [lintegral_const_mul]
      exact hF.lintegral_prod_right'
    _ = ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 8)) +
        ENNReal.ofReal C *
        (∫⁻ l : ℝ in Set.Ioi 0,
          ∫⁻ h, F h l ∂banditMeasure ν π n) := by
      congr 2
      exact lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 8)) +
        ENNReal.ofReal C *
        (∫⁻ l : ℝ in Set.Ioi 0,
          ENNReal.ofReal
            (l * Real.exp (-(3 * a / 4) * l - 3 * a ^ 2 / 32))) := by
      refine add_le_add le_rfl (mul_le_mul_left' ?_ _)
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
      have hl0 : 0 ≤ l := hl.le
      let q : ℝ := a / 4
      let t : ℝ := -(l + q) / r
      have hscore :=
        bandit_adaptive_stopped_exp_score_lintegral_le_one
          ν (gaussianBandit_isSubgaussian_one μvec)
          (π := π) i s t (n := n)
      have hevent (h : BanditHistory k n) (hh : h ∈ E) :
          S h = (s : ℝ) *
            (armFirstRewardsMean i s h - μ) := by
        exact armStoppedCenteredSum_eq_firstRewardsMean
          ν i s h hs (Nat.le_of_lt hh)
      have hfactor (h : BanditHistory k n)
          (hh : h ∈ E) (hbad : -a / 2 < U h) :
          l * Real.exp
              (l * U h - l ^ 2 / 2) ≤
            (l * Real.exp
              (-(3 * a / 4) * l - 3 * a ^ 2 / 32)) *
              Real.exp
                (t * S h - t ^ 2 / 2 *
                  ((min (armPullCount i h) s : ℕ) : ℝ)) := by
        have hmin : min (armPullCount i h) s = s :=
          min_eq_right (Nat.le_of_lt hh)
        have hX :
            (armFirstRewardsMean i s h - μ) * r < -a / 2 := by
          dsimp [U] at hbad
          nlinarith
        have hexpArg :
            l * U h - l ^ 2 / 2 ≤
              (-(3 * a / 4) * l - 3 * a ^ 2 / 32) +
                (t * S h - t ^ 2 / 2 *
                  ((min (armPullCount i h) s : ℕ) : ℝ)) := by
          rw [hmin, hevent h hh]
          dsimp [t, q, U, a]
          rw [← hrsq]
          field_simp
          nlinarith
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hexpArg) hl0
      calc
        (∫⁻ h, F h l ∂banditMeasure ν π n) ≤
            ∫⁻ h,
              if h ∈ E ∧ -a / 2 < U h then
                ENNReal.ofReal
                    (l * Real.exp
                      (-(3 * a / 4) * l - 3 * a ^ 2 / 32)) *
                  ENNReal.ofReal
                    (Real.exp
                      (t * S h - t ^ 2 / 2 *
                        ((min (armPullCount i h) s : ℕ) : ℝ)))
              else 0
              ∂banditMeasure ν π n := by
          apply lintegral_mono
          intro h
          by_cases hh : h ∈ E ∧ -a / 2 < U h
          · simp only [F, hh, if_pos]
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (hfactor h hh.1 hh.2)
          · simp [F, hh]
        _ ≤ ∫⁻ h,
              ENNReal.ofReal
                  (l * Real.exp
                    (-(3 * a / 4) * l - 3 * a ^ 2 / 32)) *
                ENNReal.ofReal
                  (Real.exp
                    (t * S h - t ^ 2 / 2 *
                      ((min (armPullCount i h) s : ℕ) : ℝ)))
              ∂banditMeasure ν π n := by
          apply lintegral_mono
          intro h
          by_cases hh : h ∈ E ∧ -a / 2 < U h <;> simp [hh]
        _ = ENNReal.ofReal
              (l * Real.exp
                (-(3 * a / 4) * l - 3 * a ^ 2 / 32)) *
            (∫⁻ h,
              ENNReal.ofReal
                (Real.exp
                  (t * S h - t ^ 2 / 2 *
                    ((min (armPullCount i h) s : ℕ) : ℝ)))
              ∂banditMeasure ν π n) := by
          rw [lintegral_const_mul]
          apply Measurable.ennreal_ofReal
          apply Measurable.exp
          apply (measurable_const.mul hS).sub
          have hminmeas : Measurable
              (fun h : BanditHistory k n ↦
                ((min (armPullCount i h) s : ℕ) : ℝ)) := by
            simpa only [Nat.cast_min] using
              (measurable_armPullCount_cast_fix i).min measurable_const
          exact measurable_const.mul hminmeas
        _ ≤ ENNReal.ofReal
              (l * Real.exp
                (-(3 * a / 4) * l - 3 * a ^ 2 / 32)) * 1 := by
          gcongr
        _ = ENNReal.ofReal
              (l * Real.exp
                (-(3 * a / 4) * l - 3 * a ^ 2 / 32)) := mul_one _
    _ = ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 8)) +
        ENNReal.ofReal C *
          (ENNReal.ofReal (Real.exp (-3 * a ^ 2 / 32)) *
            ENNReal.ofReal (1 / (3 * a / 4) ^ 2)) := by
      congr 2
      rw [show
        (fun l : ℝ ↦ ENNReal.ofReal
          (l * Real.exp (-(3 * a / 4) * l - 3 * a ^ 2 / 32))) =
        fun l ↦ ENNReal.ofReal (Real.exp (-3 * a ^ 2 / 32)) *
          ENNReal.ofReal
            (l * Real.exp (-((3 * a / 4) * l))) by
        funext l
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show
          -(3 * a / 4) * l - 3 * a ^ 2 / 32 =
            (-3 * a ^ 2 / 32) + (-(3 * a / 4 * l)) by ring,
          Real.exp_add]
        ring]
      rw [lintegral_const_mul]
      · rw [laplace_first_moment (3 * a / 4) (by positivity)]
      · apply Measurable.ennreal_ofReal
        fun_prop
    _ ≤ ENNReal.ofReal
          (2 * Real.exp (-a ^ 2 / 8) +
            2 * C / a ^ 2 * Real.exp (-3 * a ^ 2 / 32)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [← ENNReal.ofReal_mul hC.le]
      rw [← ENNReal.ofReal_add
        (by positivity)
        (mul_nonneg hC.le
          (mul_nonneg (Real.exp_nonneg _) (by positivity)))]
      apply ENNReal.ofReal_le_ofReal
      have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
      have hpos :
          0 ≤ C * Real.exp (-3 * a ^ 2 / 32) :=
        mul_nonneg hC.le (Real.exp_nonneg _)
      have hpos' :
          0 < C * Real.exp (-3 * a ^ 2 / 32) :=
        mul_pos hC (Real.exp_pos _)
      have hpos'' :
          0 < C * Real.exp (-(a ^ 2 * 3 / 32)) := by
        convert hpos' using 1 <;> ring
      field_simp [ne_of_gt ha2]
      norm_num at *
      nlinarith
    _ = ENNReal.ofReal
          (2 * Real.exp (-((s : ℝ) * ε ^ 2) / 8) +
            2 * C / ((s : ℝ) * ε ^ 2) *
              Real.exp (-(3 * (s : ℝ) * ε ^ 2) / 32)) := by
      congr 1
      dsimp [a]
      rw [mul_pow, hrsq]
      ring

end BanditAlgorithm

open BanditAlgorithm

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        ∀ (i : Fin k) (s : ℕ), 0 < s →
        ∀ ε : ℝ, 0 < ε →
        ∀ n : ℕ,
          (∫⁻ h,
              if s < armPullCount i h then
                ENNReal.ofReal
                  (1 / gaussianTSTailProb i s
                    (banditArmMean (gaussianBandit μvec) i - ε) h - 1)
              else 0
              ∂banditMeasure (gaussianBandit μvec) π n) ≤
            ENNReal.ofReal
              (2 * Real.exp (-((s : ℝ) * ε ^ 2) / 8) +
                2 * C / ((s : ℝ) * ε ^ 2) *
                  Real.exp (-(3 * (s : ℝ) * ε ^ 2) / 32)) :=
  gaussian_exact_rank_reciprocal_tail_exponential_bound_proof
