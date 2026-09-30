-- Prove2me | solution 1 for BanditAlgorithm.exp3ix_estimate_concentration_variance
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:09:32.393491+00:00
-- url     : https://prove2.me/submissions/056093d7-f326-4e78-858e-65ecb84856b8

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- The local scalar proof and complete accepted helper fragments are inlined.
See assembly.json and source-selection.json for exact provenance and hashes. -/

open scoped BigOperators

namespace Exp3IXConcentration

theorem exp_div_implicit_le {a p eta : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ eta) (hp : 0 < p) (heta : 0 < eta) :
    Real.exp (a / (p + eta / 2)) ≤ 1 + a / p := by
  have hbase : 0 < p + a / 2 := by positivity
  have hx0 : 0 ≤ a / p := div_nonneg ha0 hp.le
  have hx2 : 0 < a / p + 2 := by positivity
  have hlog : a / (p + eta / 2) ≤ Real.log (1 + a / p) := by
    calc
      a / (p + eta / 2) ≤ a / (p + a / 2) :=
        div_le_div_of_nonneg_left ha0 hbase (by linarith)
      _ = 2 * (a / p) / (a / p + 2) := by
        field_simp [hp.ne', hbase.ne', hx2.ne']
        <;> ring
      _ ≤ Real.log (1 + a / p) := Real.le_log_one_add_of_nonneg hx0
  calc
    Real.exp (a / (p + eta / 2)) ≤ Real.exp (Real.log (1 + a / p)) :=
      Real.exp_le_exp.mpr hlog
    _ = 1 + a / p := Real.exp_log (by positivity)

theorem weighted_mgf_le_one {ι : Type*} [Fintype ι]
    (p q loss : ι → ℝ) (eta : ℝ) (heta : 0 < eta)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∀ i, q i ≤ eta)
    (hl0 : ∀ i, 0 ≤ loss i) (hl1 : ∀ i, loss i ≤ 1) :
    (∑ i, p i * Real.exp (q i * loss i / (p i + eta / 2) - ∑ j, q j * loss j)) ≤ 1 := by
  have hpoint (i : ι) :
      p i * Real.exp (q i * loss i / (p i + eta / 2)) ≤ p i + q i * loss i := by
    have ha0 : 0 ≤ q i * loss i := mul_nonneg (hq0 i) (hl0 i)
    have ha : q i * loss i ≤ eta := by
      have hprod := mul_nonneg (hq0 i) (sub_nonneg.mpr (hl1 i))
      nlinarith [hq i]
    calc
      p i * Real.exp (q i * loss i / (p i + eta / 2)) ≤
          p i * (1 + q i * loss i / p i) :=
        mul_le_mul_of_nonneg_left (exp_div_implicit_le ha0 ha (hp i) heta) (hp i).le
      _ = p i + q i * loss i := by field_simp [(hp i).ne']
  have hsumexp : (∑ i, p i * Real.exp (q i * loss i / (p i + eta / 2))) ≤
      Real.exp (∑ i, q i * loss i) := by
    calc
      (∑ i, p i * Real.exp (q i * loss i / (p i + eta / 2))) ≤
          ∑ i, (p i + q i * loss i) := Finset.sum_le_sum fun i _ => hpoint i
      _ = 1 + ∑ i, q i * loss i := by rw [Finset.sum_add_distrib, hsum]
      _ ≤ Real.exp (∑ i, q i * loss i) := by
        simpa only [add_comm] using Real.add_one_le_exp (∑ i, q i * loss i)
  calc
    (∑ i, p i * Real.exp (q i * loss i / (p i + eta / 2) - ∑ j, q j * loss j)) =
        ∑ i, (p i * Real.exp (q i * loss i / (p i + eta / 2))) *
          Real.exp (-(∑ j, q j * loss j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ = (∑ i, p i * Real.exp (q i * loss i / (p i + eta / 2))) *
        Real.exp (-(∑ j, q j * loss j)) := (Finset.sum_mul _ _ _).symm
    _ ≤ Real.exp (∑ i, q i * loss i) * Real.exp (-(∑ j, q j * loss j)) :=
      mul_le_mul_of_nonneg_right hsumexp (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end Exp3IXConcentration

#print axioms Exp3IXConcentration.exp_div_implicit_le
#print axioms Exp3IXConcentration.weighted_mgf_le_one

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BanditAlgorithm

/- Verbatim helpers by Harry_Xu, accepted submission 10d5dffb-4ef9-494d-9285-ac28a45a6a44.
Original source SHA-256: 99b36fc4960ca93dc7a5bc36803453fc91b6e43a5f0e5922974455061ff92b3a. -/
private lemma expWeights_pos_ix {k : ℕ} (s : Fin k → ℝ) (i : Fin k) :
    0 < expWeights s i := by
  rw [expWeights]
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, Real.exp_pos _⟩

private lemma exp3IXProb_pos {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) : 0 < exp3IXProb η γ m h i :=
  expWeights_pos_ix _ i

private lemma exp3IXProb_sum {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) : ∑ j, exp3IXProb η γ m h j = 1 := by
  rw [show (∑ j, exp3IXProb η γ m h j) =
      (∑ j, Real.exp (-(η * exp3IXEstimate η γ m h j))) /
        (∑ j, Real.exp (-(η * exp3IXEstimate η γ m h j))) by
    simp only [exp3IXProb, expWeights, Finset.sum_div]]
  exact div_self (ne_of_gt (Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, Real.exp_pos _⟩))

private noncomputable def exp3IXIncrement {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) (z : Fin k × ℝ) : ℝ :=
  if z.1 = i then (1 - z.2) / (exp3IXProb η γ m h i + γ) else 0

private lemma exp3IXEstimate_snoc {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) (i : Fin k) :
    exp3IXEstimate η γ (m + 1) (Fin.snoc h z) i =
      exp3IXEstimate η γ m h i + exp3IXIncrement η γ m h i z := by
  simp [exp3IXEstimate, exp3IXIncrement, exp3IXProb]

/- Verbatim helpers by Grace, accepted submission ca58c058-8527-4ddb-a092-da6e213281dd.
Original source SHA-256: 1f715c21981cb921294ff4b0a662f1631944710b7f1d3a6b5b15dc01d3399ab0. -/
private def GoodAdversarialHistory {k n : ℕ} (h : BanditHistory k n) : Prop :=
  ∀ t : Fin n, (h t).2 ∈ Set.Icc (0 : ℝ) 1

private lemma measurableSet_goodAdversarialHistory {k n : ℕ} :
    MeasurableSet {h : BanditHistory k n | GoodAdversarialHistory h} := by
  rw [show {h : BanditHistory k n | GoodAdversarialHistory h} =
      ⋂ t : Fin n, (fun h : BanditHistory k n ↦ (h t).2) ⁻¹'
        Set.Icc (0 : ℝ) 1 by
    ext h
    simp only [GoodAdversarialHistory, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage]]
  have hmeas : MeasurableSet (⋂ t : Fin n,
      (fun h : BanditHistory k n ↦ (h t).2) ⁻¹' Set.Icc (0 : ℝ) 1) :=
    MeasurableSet.iInter fun t ↦
      measurableSet_Icc.preimage (measurable_snd.comp (measurable_pi_apply t))
  exact hmeas

private lemma adversarialMeasure_ae_good {k : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) :
    ∀ n : ℕ, ∀ᵐ h ∂(adversarialMeasure x π n), GoodAdversarialHistory h := by
  intro n
  induction n with
  | zero =>
      exact Filter.Eventually.of_forall fun h t ↦ t.elim0
  | succ n ih =>
      rw [adversarialMeasure]
      apply (ae_map_iff measurable_banditHistorySnoc.aemeasurable
        measurableSet_goodAdversarialHistory).2
      apply Measure.ae_compProd_of_ae_ae
        (measurableSet_goodAdversarialHistory.preimage measurable_banditHistorySnoc)
      filter_upwards [ih] with h hh
      rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
      apply (ae_map_iff (measurable_of_countable _).aemeasurable
        (measurableSet_goodAdversarialHistory.preimage
          (measurable_banditHistorySnoc.comp
            (measurable_const.prodMk measurable_id)))).2
      exact Filter.Eventually.of_forall fun a t ↦ by
        refine Fin.lastCases ?_ (fun s ↦ ?_) t
        · simpa using hx n a
        · simpa using hh s

/-
The recursive measurability argument adapts the Exp3 measurability proof in
Grace's accepted submission ca58c058-8527-4ddb-a092-da6e213281dd, lines 454-511.
The IX negative exponent and implicit-exploration denominator are handled here.
-/
private lemma exp3IXEstimate_measurable {k : ℕ} (η γ : ℝ) :
    ∀ (m : ℕ) (i : Fin k),
      Measurable (fun h : BanditHistory k m ↦ exp3IXEstimate η γ m h i) := by
  intro m
  induction m with
  | zero =>
      intro i
      simp [exp3IXEstimate]
  | succ m ih =>
      intro i
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hold : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            exp3IXEstimate η γ m (Fin.init h) i) := (ih i).comp hinit
      have hprob : Measurable
          (fun h : BanditHistory k (m + 1) ↦ exp3IXProb η γ m (Fin.init h) i) := by
        unfold exp3IXProb expWeights
        apply Measurable.div
        · exact Real.continuous_exp.measurable.comp
            (measurable_const.mul ((ih i).comp hinit)).neg
        · apply Finset.measurable_sum
          intro j hj
          exact Real.continuous_exp.measurable.comp
            (measurable_const.mul ((ih j).comp hinit)).neg
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hcond : MeasurableSet
          {h : BanditHistory k (m + 1) | (h (Fin.last m)).1 = i} := by
        simpa only [Set.mem_singleton_iff] using
          (measurableSet_singleton i).preimage (measurable_fst.comp hlast)
      have hfrac : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            (1 - (h (Fin.last m)).2) / (exp3IXProb η γ m (Fin.init h) i + γ)) :=
        (measurable_const.sub (measurable_snd.comp hlast)).div
          (hprob.add measurable_const)
      have hinc : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            if (h (Fin.last m)).1 = i then
              (1 - (h (Fin.last m)).2) / (exp3IXProb η γ m (Fin.init h) i + γ)
            else 0) := Measurable.ite hcond hfrac measurable_const
      simpa only [exp3IXEstimate, exp3IXProb] using hold.add hinc

private noncomputable def ixStat {k : ℕ} (η : ℝ)
    (x : ℕ → Fin k → ℝ) (q : Fin k → ℝ) (m : ℕ)
    (h : BanditHistory k m) : ℝ :=
  ∑ i, q i * (exp3IXEstimate η (η / 2) m h i - ∑ t : Fin m, (1 - x t i))

private lemma ixStat_measurable {k : ℕ} (η : ℝ)
    (x : ℕ → Fin k → ℝ) (q : Fin k → ℝ) (m : ℕ) :
    Measurable (ixStat η x q m) := by
  unfold ixStat
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.mul ((exp3IXEstimate_measurable η (η / 2) m i).sub
    measurable_const)

private lemma ixStat_exp_measurable {k : ℕ} (η : ℝ)
    (x : ℕ → Fin k → ℝ) (q : Fin k → ℝ) (m : ℕ) :
    Measurable (fun h ↦ ENNReal.ofReal (Real.exp (ixStat η x q m h))) :=
  (Real.continuous_exp.measurable.comp (ixStat_measurable η x q m)).ennreal_ofReal

private lemma ixStat_snoc {k : ℕ} (η : ℝ)
    (x : ℕ → Fin k → ℝ) (q : Fin k → ℝ) (m : ℕ)
    (h : BanditHistory k m) (a : Fin k) :
    ixStat η x q (m + 1) (Fin.snoc h (a, x m a)) =
      ixStat η x q m h +
        q a * (1 - x m a) / (exp3IXProb η (η / 2) m h a + η / 2) -
        ∑ i, q i * (1 - x m i) := by
  classical
  have hloss (i : Fin k) :
      (∑ t : Fin (m + 1), (1 - x t i)) =
        (∑ t : Fin m, (1 - x t i)) + (1 - x m i) := by
    rw [Fin.sum_univ_castSucc]
    rfl
  have hinc :
      (∑ i, q i * exp3IXIncrement η (η / 2) m h i (a, x m a)) =
        q a * (1 - x m a) / (exp3IXProb η (η / 2) m h a + η / 2) := by
    rw [Finset.sum_eq_single a]
    · simp [exp3IXIncrement, mul_div_assoc]
    · intro b hb hba
      simp [exp3IXIncrement, Ne.symm hba]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  unfold ixStat
  simp_rw [exp3IXEstimate_snoc, hloss]
  calc
    _ = (∑ i, q i * (exp3IXEstimate η (η / 2) m h i -
          ∑ t : Fin m, (1 - x t i))) +
        (∑ i, q i * exp3IXIncrement η (η / 2) m h i (a, x m a)) -
        ∑ i, q i * (1 - x m i) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hinc]

private lemma adversarialStep_lintegral_ix {k : ℕ}
    (η : ℝ) (x : ℕ → Fin k → ℝ) (π : BanditPolicy k)
    (hπ : IsExp3IXPolicy η (η / 2) π) (m : ℕ) (h : BanditHistory k m)
    (f : Fin k × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂adversarialStepKernel x π m h) =
      ∑ a, ENNReal.ofReal (exp3IXProb η (η / 2) m h a) * f (a, x m a) := by
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
  rw [lintegral_map hf (measurable_of_countable _), hπ m h]
  simp only [lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]

private lemma ixStat_step_lintegral_le {k : ℕ} (hk : 0 < k)
    (η : ℝ) (hη : 0 < η) (x : ℕ → Fin k → ℝ)
    (hx : ∀ t i, x t i ∈ Set.Icc (0 : ℝ) 1)
    (q : Fin k → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) η)
    (π : BanditPolicy k) (hπ : IsExp3IXPolicy η (η / 2) π)
    (m : ℕ) (h : BanditHistory k m) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (ixStat η x q (m + 1) (Fin.snoc h z)))
      ∂adversarialStepKernel x π m h) ≤
      ENNReal.ofReal (Real.exp (ixStat η x q m h)) := by
  let p : Fin k → ℝ := exp3IXProb η (η / 2) m h
  let l : Fin k → ℝ := fun i ↦ 1 - x m i
  have hp (i : Fin k) : 0 < p i := exp3IXProb_pos η (η / 2) m h i
  have hpsum : ∑ i, p i = 1 := exp3IXProb_sum η (η / 2) m h ⟨0, hk⟩
  have hl (i : Fin k) : l i ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [l]
    constructor <;> linarith [(hx m i).1, (hx m i).2]
  have hweighted := Exp3IXConcentration.weighted_mgf_le_one
    p q l η hη hp hpsum (fun i ↦ (hq i).1) (fun i ↦ (hq i).2)
      (fun i ↦ (hl i).1) (fun i ↦ (hl i).2)
  have hreal :
      (∑ a, p a * Real.exp (ixStat η x q (m + 1) (Fin.snoc h (a, x m a)))) ≤
        Real.exp (ixStat η x q m h) := by
    calc
      _ = Real.exp (ixStat η x q m h) *
          (∑ a, p a * Real.exp (q a * l a / (p a + η / 2) -
            ∑ i, q i * l i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [ixStat_snoc]
        change p a * Real.exp (ixStat η x q m h + q a * l a / (p a + η / 2) -
          ∑ i, q i * l i) = _
        rw [show ixStat η x q m h + q a * l a / (p a + η / 2) -
            (∑ i, q i * l i) =
              ixStat η x q m h + (q a * l a / (p a + η / 2) -
                ∑ i, q i * l i) by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (ixStat η x q m h) * 1 :=
        mul_le_mul_of_nonneg_left hweighted (Real.exp_pos _).le
      _ = _ := mul_one _
  have hf : Measurable
      (fun z ↦ ENNReal.ofReal (Real.exp (ixStat η x q (m + 1) (Fin.snoc h z)))) :=
    (ixStat_exp_measurable η x q (m + 1)).comp
      (measurable_banditHistorySnoc.comp (measurable_const.prodMk measurable_id))
  rw [adversarialStep_lintegral_ix η x π hπ m h _ hf]
  change (∑ a, ENNReal.ofReal (p a) *
    ENNReal.ofReal (Real.exp (ixStat η x q (m + 1) (Fin.snoc h (a, x m a))))) ≤ _
  simp_rw [← ENNReal.ofReal_mul (hp _).le]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun a _ ↦ mul_nonneg (hp a).le (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal hreal

private lemma ixStat_mgf_le_one {k : ℕ} (hk : 0 < k)
    (η : ℝ) (hη : 0 < η) (x : ℕ → Fin k → ℝ)
    (hx : ∀ t i, x t i ∈ Set.Icc (0 : ℝ) 1)
    (q : Fin k → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) η)
    (π : BanditPolicy k) (hπ : IsExp3IXPolicy η (η / 2) π) :
    ∀ n : ℕ, (∫⁻ h, ENNReal.ofReal (Real.exp (ixStat η x q n h))
      ∂adversarialMeasure x π n) ≤ 1 := by
  intro n
  induction n with
  | zero =>
      simp [adversarialMeasure, ixStat, exp3IXEstimate]
  | succ m ih =>
      rw [adversarialMeasure]
      rw [lintegral_map (ixStat_exp_measurable η x q (m + 1))
        measurable_banditHistorySnoc]
      have hm : Measurable (fun a : BanditHistory k m × (Fin k × ℝ) ↦
          ENNReal.ofReal (Real.exp (ixStat η x q (m + 1) (Fin.snoc a.1 a.2)))) :=
        (ixStat_exp_measurable η x q (m + 1)).comp measurable_banditHistorySnoc
      rw [Measure.lintegral_compProd hm]
      exact (lintegral_mono (fun h ↦
        ixStat_step_lintegral_le hk η hη x hx q hq π hπ m h)).trans ih

private lemma ixStat_tail_le {k : ℕ} (hk : 0 < k)
    (η : ℝ) (hη : 0 < η) (x : ℕ → Fin k → ℝ)
    (hx : ∀ t i, x t i ∈ Set.Icc (0 : ℝ) 1)
    (q : Fin k → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) η)
    (π : BanditPolicy k) (hπ : IsExp3IXPolicy η (η / 2) π)
    (n : ℕ) (b : ℝ) (hb : 0 < b) :
    adversarialMeasure x π n {h | Real.log b ≤ ixStat η x q n h} ≤
      ENNReal.ofReal (1 / b) := by
  have hsub : {h | Real.log b ≤ ixStat η x q n h} ⊆
      {h | ENNReal.ofReal b ≤ ENNReal.ofReal (Real.exp (ixStat η x q n h))} := by
    intro h hh
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_log hb]
    exact Real.exp_le_exp.mpr hh
  calc
    _ ≤ adversarialMeasure x π n
        {h | ENNReal.ofReal b ≤ ENNReal.ofReal (Real.exp (ixStat η x q n h))} :=
      measure_mono hsub
    _ ≤ (∫⁻ h, ENNReal.ofReal (Real.exp (ixStat η x q n h))
        ∂adversarialMeasure x π n) / ENNReal.ofReal b :=
      meas_ge_le_lintegral_div (ixStat_exp_measurable η x q n).aemeasurable
        (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top
    _ ≤ 1 / ENNReal.ofReal b := ENNReal.div_le_div_right
      (ixStat_mgf_le_one hk η hη x hx q hq π hπ n) _
    _ = ENNReal.ofReal (1 / b) := by
      rw [ENNReal.ofReal_div_of_pos hb, ENNReal.ofReal_one]

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp3IXPolicy η (η / 2) π) :
    BanditAlgorithm.adversarialMeasure x π n
      {h : BanditAlgorithm.BanditHistory k n |
        (∃ t : Fin n, (h t).2 ∉ Set.Icc (0 : ℝ) 1) ∨
        Real.log ((k + 1) / δ) / η ≤
          (⨆ i : Fin k,
            BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
              ∑ t : Fin n, (1 - x t i)) ∨
        Real.log ((k + 1) / δ) / η ≤
          ∑ i : Fin k,
            (BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
              ∑ t : Fin n, (1 - x t i))} ≤
      ENNReal.ofReal δ := by
  classical
  have hk0 : 0 < k := by omega
  letI : Nonempty (Fin k) := ⟨⟨0, hk0⟩⟩
  let μ := adversarialMeasure x π n
  let d : BanditHistory k n → Fin k → ℝ := fun h i ↦
    exp3IXEstimate η (η / 2) n h i - ∑ t : Fin n, (1 - x t i)
  let b : ℝ := ((k : ℝ) + 1) / δ
  let e : ℝ := δ / ((k : ℝ) + 1)
  let τ : ℝ := Real.log b / η
  let Arm : Fin k → Set (BanditHistory k n) := fun i ↦ {h | τ ≤ d h i}
  let Sum : Set (BanditHistory k n) := {h | τ ≤ ∑ i, d h i}
  let Bad : Set (BanditHistory k n) :=
    {h | ∃ t : Fin n, (h t).2 ∉ Set.Icc (0 : ℝ) 1}
  have hK : 0 < (k : ℝ) + 1 := by positivity
  have hb : 0 < b := div_pos hK hδ.1
  have he : 0 ≤ e := div_nonneg hδ.1.le hK.le
  have hbe : 1 / b = e := by
    dsimp [b, e]
    field_simp [hδ.1.ne', hK.ne']
  have hArm (i : Fin k) : μ (Arm i) ≤ ENNReal.ofReal e := by
    let q : Fin k → ℝ := fun j ↦ if j = i then η else 0
    have hq (j : Fin k) : q j ∈ Set.Icc (0 : ℝ) η := by
      dsimp [q]
      split_ifs <;> constructor <;> linarith
    have hstat (h : BanditHistory k n) : ixStat η x q n h = η * d h i := by
      simp [ixStat, q, d, ite_mul]
    have hsub : Arm i ⊆ {h | Real.log b ≤ ixStat η x q n h} := by
      intro h hh
      change Real.log b ≤ ixStat η x q n h
      rw [hstat]
      have hh' : Real.log b / η ≤ d h i := hh
      simpa [mul_comm] using (div_le_iff₀ hη).mp hh'
    have ht := ixStat_tail_le hk0 η hη x hx q hq π hπ n b hb
    rw [hbe] at ht
    exact (measure_mono hsub).trans ht
  have hSum : μ Sum ≤ ENNReal.ofReal e := by
    let q : Fin k → ℝ := fun _ ↦ η
    have hq (j : Fin k) : q j ∈ Set.Icc (0 : ℝ) η := ⟨hη.le, le_rfl⟩
    have hstat (h : BanditHistory k n) : ixStat η x q n h = η * ∑ i, d h i := by
      simp only [ixStat, q, d, Finset.mul_sum]
    have hsub : Sum ⊆ {h | Real.log b ≤ ixStat η x q n h} := by
      intro h hh
      change Real.log b ≤ ixStat η x q n h
      rw [hstat]
      have hh' : Real.log b / η ≤ ∑ i, d h i := hh
      simpa [mul_comm] using (div_le_iff₀ hη).mp hh'
    have ht := ixStat_tail_le hk0 η hη x hx q hq π hπ n b hb
    rw [hbe] at ht
    exact (measure_mono hsub).trans ht
  have hBad : μ Bad = 0 := by
    have hgood := adversarialMeasure_ae_good x hx π n
    simpa only [ae_iff, GoodAdversarialHistory, not_forall] using hgood
  have hUnion : μ (⋃ i, Arm i) ≤ ∑ _i : Fin k, ENNReal.ofReal e := by
    exact (measure_iUnion_fintype_le μ Arm).trans
      (Finset.sum_le_sum (fun i _ ↦ hArm i))
  have htotal : (∑ _i : Fin k, e) + e = δ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [e]
    field_simp [hK.ne']
    <;> ring
  have hsum_e : (∑ _i : Fin k, ENNReal.ofReal e) + ENNReal.ofReal e =
      ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ he)]
    rw [← ENNReal.ofReal_add (Finset.sum_nonneg (fun _ _ ↦ he)) he, htotal]
  change μ {h | h ∈ Bad ∨ τ ≤ (⨆ i : Fin k, d h i) ∨ h ∈ Sum} ≤ _
  have hsub : {h | h ∈ Bad ∨ τ ≤ (⨆ i : Fin k, d h i) ∨ h ∈ Sum} ⊆
      Bad ∪ ((⋃ i, Arm i) ∪ Sum) := by
    intro h hh
    rcases hh with hbad | hmax | hsum
    · exact Or.inl hbad
    · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := d h)
      apply Or.inr
      apply Or.inl
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change τ ≤ d h i
      rw [hi]
      exact hmax
    · exact Or.inr (Or.inr hsum)
  calc
    _ ≤ μ (Bad ∪ ((⋃ i, Arm i) ∪ Sum)) := measure_mono hsub
    _ ≤ μ Bad + μ ((⋃ i, Arm i) ∪ Sum) := measure_union_le _ _
    _ ≤ μ Bad + (μ (⋃ i, Arm i) + μ Sum) :=
      add_le_add le_rfl (measure_union_le _ _)
    _ = μ (⋃ i, Arm i) + μ Sum := by rw [hBad, zero_add]
    _ ≤ (∑ _i : Fin k, ENNReal.ofReal e) + ENNReal.ofReal e :=
      add_le_add hUnion hSum
    _ = ENNReal.ofReal δ := hsum_e

#print axioms solution
