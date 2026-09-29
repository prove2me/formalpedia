-- Prove2me | solution 1 for MeasureTheory.uniformIntegrable_one_of_sq_bounded_approx
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T10:57:55.591907+00:00
-- url     : https://prove2.me/submissions/dc0e46d9-8af6-4efa-9dcb-eb0489b065e9

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cauchy–Schwarz: the integral of a nonnegative `L²` function over a set is bounded by the
`L²` norm times the square root of the measure of the set. -/
private theorem setIntegral_le_sqrt_mul_sqrt_measure (P : Measure Ω) [IsProbabilityMeasure P] (u : Ω → ℝ)
    (hu0 : ∀ ω, 0 ≤ u ω) (hu2 : MemLp u 2 P) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ ω in s, u ω ∂P ≤ Real.sqrt (∫ ω, (u ω) ^ 2 ∂P) * Real.sqrt (P s).toReal := by
  have hind : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 P := (memLp_const (1 : ℝ)).indicator hs
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) Real.HolderConjugate.two_two
    (f := u) (g := s.indicator (fun _ => (1 : ℝ)))
    (Eventually.of_forall fun ω => hu0 ω)
    (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (by simpa [ENNReal.ofReal_ofNat] using hu2) (by simpa [ENNReal.ofReal_ofNat] using hind)
  have hlhs : ∫ ω, u ω * s.indicator (fun _ => (1 : ℝ)) ω ∂P = ∫ ω in s, u ω ∂P := by
    rw [← integral_indicator hs]
    congr 1
    funext ω
    by_cases h : ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hpow : ∀ g : Ω → ℝ, (∫ ω, g ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
      = Real.sqrt (∫ ω, (g ω) ^ 2 ∂P) := by
    intro g
    have h : ∫ ω, g ω ^ (2 : ℝ) ∂P = ∫ ω, (g ω) ^ 2 ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp
    rw [h, Real.sqrt_eq_rpow]
  rw [hlhs, hpow u, hpow _] at h2
  have e2 : ∫ ω, (s.indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂P = (P s).toReal := by
    have h : ∀ ω, (s.indicator (fun _ => (1 : ℝ)) ω) ^ 2 = s.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω; by_cases h : ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    simp only [h]
    rw [integral_indicator hs]
    simp [measureReal_def]
  rwa [e2] at h2

/-- For a nonnegative integrable function the integral over `{g ≥ D}` is arbitrarily small once
the threshold `D` is large. -/
private theorem exists_tail_setIntegral_le (P : Measure Ω) (g : Ω → ℝ)
    (hg : Integrable g P) (hgm : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, C ≤ D → ∫ ω in {ω | D ≤ g ω}, g ω ∂P ≤ ε := by
  have hmeas : ∀ k : ℕ, MeasurableSet {ω | (k : ℝ) ≤ g ω} :=
    fun k => measurableSet_le measurable_const hgm
  have htend : Tendsto (fun k : ℕ => ∫ ω, Set.indicator {ω | (k : ℝ) ≤ g ω} g ω ∂P)
      atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := P) (F := fun (k : ℕ) ω =>
        Set.indicator {ω | (k : ℝ) ≤ g ω} g ω) (f := fun _ => (0 : ℝ)) (bound := g) (l := atTop)
      (Eventually.of_forall fun k => (hg.indicator (hmeas k)).aestronglyMeasurable)
      (Eventually.of_forall fun k => Eventually.of_forall fun ω => by
        rcases Set.indicator_eq_zero_or_self {ω | (k : ℝ) ≤ g ω} g ω with h | h
        · simp [h, hg0 ω]
        · simp [h, abs_of_nonneg (hg0 ω)])
      hg
      (Eventually.of_forall fun ω => ?_)
    · simpa using h
    · obtain ⟨k, hk⟩ := exists_nat_gt (g ω)
      refine tendsto_atTop_of_eventually_const (i₀ := k) fun j hj => ?_
      have hne : ¬ ((j : ℝ) ≤ g ω) := by
        have : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        linarith
      simp [Set.indicator_of_notMem, hne]
  obtain ⟨k, hk⟩ := (htend.eventually (gt_mem_nhds hε)).exists
  refine ⟨max 1 k, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun D hD => ?_⟩
  have hsub : {ω | D ≤ g ω} ⊆ {ω | (k : ℝ) ≤ g ω} := fun ω hω =>
    le_trans (le_trans (le_max_right 1 (k : ℝ)) hD) hω
  calc ∫ ω in {ω | D ≤ g ω}, g ω ∂P ≤ ∫ ω in {ω | (k : ℝ) ≤ g ω}, g ω ∂P :=
        setIntegral_mono_set hg.integrableOn (Eventually.of_forall hg0)
          (HasSubset.Subset.eventuallyLE hsub)
    _ = ∫ ω, Set.indicator {ω | (k : ℝ) ≤ g ω} g ω ∂P := (integral_indicator (hmeas k)).symm
    _ ≤ ε := le_of_lt hk

/-- The `L¹`-seminorm of the restriction of a nonnegative integrable function to a measurable
set is the (real) integral over that set. -/
private theorem eLpNorm_one_indicator_eq_ofReal_setIntegral (P : Measure Ω) (g : Ω → ℝ)
    (hg : Integrable g P) (hg0 : ∀ ω, 0 ≤ g ω) {s : Set Ω} (hs : MeasurableSet s) :
    eLpNorm (s.indicator g) 1 P = ENNReal.ofReal (∫ ω in s, g ω ∂P) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← integral_indicator hs,
    ofReal_integral_eq_lintegral_ofReal (hg.indicator hs)
      (Eventually.of_forall fun ω => Set.indicator_nonneg (fun x _ => hg0 x) ω)]
  refine lintegral_congr fun ω => ?_
  rw [Real.enorm_eq_ofReal (Set.indicator_nonneg (fun x _ => hg0 x) ω)]


end Helpers

theorem solution {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (hfm : ∀ n, Measurable (f n)) (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfint : ∀ n, Integrable (f n) P) (hfle : ∀ n, ∫ ω, f n ω ∂P ≤ 1)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ u w : ℕ → Ω → ℝ, ∃ M : ℝ, 0 ≤ M ∧
      (∀ n, N ≤ n → MemLp (u n) 2 P) ∧ (∀ n, N ≤ n → Integrable (w n) P) ∧
      (∀ n, N ≤ n → ∀ ω, 0 ≤ u n ω) ∧ (∀ n, N ≤ n → ∀ ω, 0 ≤ w n ω) ∧
      (∀ n, N ≤ n → ∀ ω, f n ω ≤ u n ω + w n ω) ∧
      (∀ n, N ≤ n → ∫ ω, (u n ω) ^ 2 ∂P ≤ M) ∧
      (∀ n, N ≤ n → ∫ ω, w n ω ∂P ≤ ε)) :
    UniformIntegrable f 1 P := by
  refine uniformIntegrable_of (le_refl 1) (by simp)
    (fun n => (hfm n).aestronglyMeasurable) ?_
  intro ε hε
  obtain ⟨N, u, w, M, hM0, hu2, hwint, hu0, hw0, hle, huM, hwε⟩ := hdec (ε / 2) (by linarith)
  choose Cn hCn0 hCnb using fun n =>
    exists_tail_setIntegral_le P (f n) (hfint n) (hfm n) (fun ω => hf0 n ω) hε
  set C : ℝ := max (4 * M / ε ^ 2 + 1) (∑ k ∈ Finset.range N, Cn k) with hC
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hCbig : 4 * M / ε ^ 2 + 1 ≤ C := le_max_left _ _
  have hCsmall : ∀ n, n < N → Cn n ≤ C := by
    intro n hn
    refine le_trans ?_ (le_max_right _ _)
    exact Finset.single_le_sum (f := Cn) (fun k _ => (hCn0 k).le) (Finset.mem_range.2 hn)
  refine ⟨C.toNNReal, fun n => ?_⟩
  have hCcoe : ((C.toNNReal : ℝ≥0) : ℝ) = C := Real.coe_toNNReal C hCpos.le
  have hset : {x | C.toNNReal ≤ ‖f n x‖₊} = {ω | C ≤ f n ω} := by
    ext x
    simp only [Set.mem_setOf_eq, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, hCcoe,
      abs_of_nonneg (hf0 n x)]
  have hsmeas : MeasurableSet {ω | C ≤ f n ω} := measurableSet_le measurable_const (hfm n)
  rw [hset, eLpNorm_one_indicator_eq_ofReal_setIntegral P (f n) (hfint n) (hf0 n) hsmeas]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hn : N ≤ n
  · -- the interesting range: split into the `L²`-bounded part and the small part
    have huint : Integrable (u n) P := (hu2 n hn).integrable (by norm_num)
    have hsum_int : Integrable (fun ω => u n ω + w n ω) P := huint.add (hwint n hn)
    have hstep1 : ∫ ω in {ω | C ≤ f n ω}, f n ω ∂P
        ≤ ∫ ω in {ω | C ≤ f n ω}, (u n ω + w n ω) ∂P := by
      refine setIntegral_mono_on (hfint n).integrableOn hsum_int.integrableOn hsmeas ?_
      intro ω _
      exact hle n hn ω
    have hstep2 : ∫ ω in {ω | C ≤ f n ω}, (u n ω + w n ω) ∂P
        = (∫ ω in {ω | C ≤ f n ω}, u n ω ∂P) + ∫ ω in {ω | C ≤ f n ω}, w n ω ∂P :=
      integral_add huint.integrableOn (hwint n hn).integrableOn
    -- the tail part is small in `L¹`
    have hwbound : ∫ ω in {ω | C ≤ f n ω}, w n ω ∂P ≤ ε / 2 := by
      refine le_trans ?_ (hwε n hn)
      refine setIntegral_le_integral (hwint n hn) ?_
      exact Eventually.of_forall fun ω => hw0 n hn ω
    -- the bounded part is controlled by Cauchy–Schwarz and Markov's inequality
    have hmarkov : C * (P {ω | C ≤ f n ω}).toReal ≤ 1 := by
      refine le_trans ?_ (hfle n)
      simpa [measureReal_def] using
        mul_meas_ge_le_integral_of_nonneg (μ := P)
          (Eventually.of_forall fun ω => hf0 n ω) (hfint n) C
    have hmeasle : (P {ω | C ≤ f n ω}).toReal ≤ 1 / C := by
      rw [le_div_iff₀ hCpos]
      linarith [hmarkov]
    have hcs := setIntegral_le_sqrt_mul_sqrt_measure P (u n) (hu0 n hn) (hu2 n hn) hsmeas
    have hsqrtM : Real.sqrt (∫ ω, (u n ω) ^ 2 ∂P) ≤ Real.sqrt M :=
      Real.sqrt_le_sqrt (huM n hn)
    have hsqrtmeas : Real.sqrt (P {ω | C ≤ f n ω}).toReal ≤ Real.sqrt (1 / C) :=
      Real.sqrt_le_sqrt hmeasle
    have hubound : ∫ ω in {ω | C ≤ f n ω}, u n ω ∂P ≤ Real.sqrt M * Real.sqrt (1 / C) := by
      refine hcs.trans (mul_le_mul hsqrtM hsqrtmeas (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hfinal : Real.sqrt M * Real.sqrt (1 / C) ≤ ε / 2 := by
      have hMC : M / C ≤ (ε / 2) ^ 2 := by
        rw [div_le_iff₀ hCpos]
        have h1 : 4 * M / ε ^ 2 ≤ C := by linarith
        have h2 : 4 * M ≤ C * ε ^ 2 := by
          rw [div_le_iff₀ (by positivity)] at h1
          linarith
        nlinarith [sq_nonneg ε]
      have : Real.sqrt M * Real.sqrt (1 / C) = Real.sqrt (M / C) := by
        rw [← Real.sqrt_mul hM0]
        ring_nf
      rw [this]
      calc Real.sqrt (M / C) ≤ Real.sqrt ((ε / 2) ^ 2) := Real.sqrt_le_sqrt hMC
        _ = ε / 2 := Real.sqrt_sq (by linarith)
    linarith [hstep1, hstep2.le, hstep2.ge, hubound, hwbound, hfinal]
  · -- finitely many exceptional indices, each handled by integrability
    exact hCnb n C (hCsmall n (lt_of_not_ge hn))
