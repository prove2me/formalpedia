-- Prove2me | solution 1 for MarkovChainCLT.abs_integral_prod_sub_prod_integral_le_of_alpha
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T09:08:58.863482+00:00
-- url     : https://prove2.me/submissions/8a73cc30-4b10-4c8e-9d8f-5818472c6757

import Theorems.Thm_MarkovChainCLT_alpha_cov_bounded_complex
import Theorems.Thm_MarkovChainCLT_processSigma_le_of_measurable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

private theorem processSigma_mono (Y : ℕ → Ω → E) {s t : Set ℕ} (h : s ⊆ t) :
    processSigma Y s ≤ processSigma Y t := by
  refine iSup₂_le fun i hi => ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ t) => MeasurableSpace.comap (Y i) inferInstance) i (h hi)

private theorem alphaMixingCoef_nonneg' (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (n : ℕ) : 0 ≤ alphaMixingCoef P Y n := by
  refine le_csSup ⟨1, ?_⟩
    ⟨0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
      @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩
  rintro r ⟨k, A, B, -, -, rfl⟩
  have hAB1 : (P (A ∩ B)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
      (measure_mono (Set.subset_univ (A ∩ B)))
  have hA1 : (P A).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ) (measure_mono (Set.subset_univ A))
  have hB1 : (P B).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ) (measure_mono (Set.subset_univ B))
  have hA0 : (0 : ℝ) ≤ (P A).toReal := ENNReal.toReal_nonneg
  have hB0 : (0 : ℝ) ≤ (P B).toReal := ENNReal.toReal_nonneg
  have hAB0 : (0 : ℝ) ≤ (P (A ∩ B)).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> nlinarith

theorem solution (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ i, Measurable (Y i)) (n : ℕ) (a b : ℕ → ℕ) (f : ℕ → Ω → ℂ) (M : ℕ → ℝ) (m : ℕ)
    (hab : ∀ j, j < m → a j ≤ b j)
    (hgap : ∀ j, j + 1 < m → b j + n ≤ a (j + 1))
    (hf : ∀ j, j < m → Measurable[processSigma Y (Set.Icc (a j) (b j))] (f j))
    (hM : ∀ j, j < m → 0 ≤ M j)
    (hfb : ∀ j, j < m → ∀ ω, ‖f j ω‖ ≤ M j) :
    ‖(∫ ω, ∏ j ∈ Finset.range m, f j ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P‖
      ≤ 16 * ((m - 1 : ℕ) : ℝ) * alphaMixingCoef P Y n * ∏ j ∈ Finset.range m, M j := by
  have halpha : 0 ≤ alphaMixingCoef P Y n := alphaMixingCoef_nonneg' P Y n
  suffices H : ∀ m : ℕ, (∀ j, j < m → a j ≤ b j) → (∀ j, j + 1 < m → b j + n ≤ a (j + 1)) →
      (∀ j, j < m → Measurable[processSigma Y (Set.Icc (a j) (b j))] (f j)) →
      (∀ j, j < m → 0 ≤ M j) → (∀ j, j < m → ∀ ω, ‖f j ω‖ ≤ M j) →
      ‖(∫ ω, ∏ j ∈ Finset.range m, f j ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P‖
        ≤ 16 * ((m - 1 : ℕ) : ℝ) * alphaMixingCoef P Y n * ∏ j ∈ Finset.range m, M j from
    H m hab hgap hf hM hfb
  clear hab hgap hf hM hfb m
  intro m
  induction m with
  | zero => intro _ _ _ _ _; simp
  | succ m ih =>
    intro hab hgap hf hM hfb
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp
    obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    -- restricted hypotheses, for the induction hypothesis
    have hab' : ∀ j, j < m → a j ≤ b j := fun j hj => hab j (Nat.lt_succ_of_lt hj)
    have hgap' : ∀ j, j + 1 < m → b j + n ≤ a (j + 1) := fun j hj =>
      hgap j (Nat.lt_succ_of_lt hj)
    have hf' : ∀ j, j < m → Measurable[processSigma Y (Set.Icc (a j) (b j))] (f j) :=
      fun j hj => hf j (Nat.lt_succ_of_lt hj)
    have hM' : ∀ j, j < m → 0 ≤ M j := fun j hj => hM j (Nat.lt_succ_of_lt hj)
    have hfb' : ∀ j, j < m → ∀ ω, ‖f j ω‖ ≤ M j := fun j hj => hfb j (Nat.lt_succ_of_lt hj)
    have hIH := ih hab' hgap' hf' hM' hfb'
    set G : Ω → ℂ := fun ω => ∏ j ∈ Finset.range m, f j ω with hG
    set K : ℝ := ∏ j ∈ Finset.range m, M j with hK
    have hKnonneg : 0 ≤ K := Finset.prod_nonneg fun j hj => hM' j (Finset.mem_range.mp hj)
    have hMm : 0 ≤ M m := hM m (Nat.lt_succ_self m)
    -- `b` is nondecreasing along the block schedule
    have hstep : ∀ j, j < m → b j ≤ b (j + 1) := by
      intro j hj
      have h1 : b j + n ≤ a (j + 1) := hgap j (by omega)
      have h2 : a (j + 1) ≤ b (j + 1) := hab (j + 1) (by omega)
      omega
    have hmono : ∀ i j : ℕ, i ≤ j → j ≤ m → b i ≤ b j := by
      intro i j hij hjm
      induction j with
      | zero => simp_all
      | succ j ihj =>
        rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · have h1 : b i ≤ b j := ihj (by omega) (by omega)
          exact h1.trans (hstep j (by omega))
        · have : i = j + 1 := by omega
          subst this
          exact le_rfl
    -- measurability of the partial product with respect to the past
    have hGmeas : Measurable[processSigma Y (Set.Iic (b p))] G := by
      refine Finset.measurable_prod _ fun j hj => ?_
      have hjm : j < m := Finset.mem_range.mp hj
      refine (hf' j hjm).mono (processSigma_mono Y ?_) le_rfl
      intro x hx
      have hxb : x ≤ b j := hx.2
      have : b j ≤ b p := hmono j p (by omega) (by omega)
      exact le_trans hxb this
    -- measurability of the last factor with respect to the future
    have hfmmeas : Measurable[processSigma Y (Set.Ici (b p + n))] (f m) := by
      refine (hf m (Nat.lt_succ_self m)).mono (processSigma_mono Y ?_) le_rfl
      intro x hx
      have h1 : b p + n ≤ a (p + 1) := hgap p (by omega)
      have h2 : a m ≤ x := hx.1
      have : b p + n ≤ a m := by rw [hp]; exact h1
      exact le_trans this h2
    -- bounds
    have hGb : ∀ ω, ‖G ω‖ ≤ K := by
      intro ω
      have hnp : ‖G ω‖ = ∏ j ∈ Finset.range m, ‖f j ω‖ := by
        rw [hG]; exact Complex.norm_prod _ _
      rw [hnp]
      exact Finset.prod_le_prod (fun j _ => norm_nonneg _)
        (fun j hj => hfb' j (Finset.mem_range.mp hj) ω)
    have hfmb : ∀ ω, ‖f m ω‖ ≤ M m := hfb m (Nat.lt_succ_self m)
    have hintfm : ‖∫ ω, f m ω ∂P‖ ≤ M m := by
      have := norm_integral_le_of_norm_le_const (μ := P) (C := M m)
        (Filter.Eventually.of_forall hfmb)
      simpa using this
    -- the pairwise estimate at the last junction
    have hpair := MarkovChainCLT.alpha_cov_bounded_complex P Y hY n (b p) G (f m) hGmeas
      hfmmeas K (M m) hKnonneg hMm hGb hfmb
    -- split the error into the junction error and the inductive error
    have hsplit : (∫ ω, ∏ j ∈ Finset.range (m + 1), f j ω ∂P)
          - ∏ j ∈ Finset.range (m + 1), ∫ ω, f j ω ∂P
        = ((∫ ω, G ω * f m ω ∂P) - (∫ ω, G ω ∂P) * (∫ ω, f m ω ∂P))
          + ((∫ ω, G ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P) * (∫ ω, f m ω ∂P) := by
      simp only [Finset.prod_range_succ, hG]
      ring
    have hbound2 : ‖((∫ ω, G ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P)
        * (∫ ω, f m ω ∂P)‖ ≤ (16 * ((m - 1 : ℕ) : ℝ) * alphaMixingCoef P Y n * K) * M m := by
      rw [norm_mul]
      exact mul_le_mul hIH hintfm (norm_nonneg _)
        (by positivity)
    have hcast : ((m + 1 - 1 : ℕ) : ℝ) = (m : ℝ) := by simp
    have hcast2 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : (1 : ℕ) ≤ m := hmpos
      push_cast [Nat.cast_sub this]
      ring
    rw [hsplit, Finset.prod_range_succ, hcast]
    calc ‖((∫ ω, G ω * f m ω ∂P) - (∫ ω, G ω ∂P) * (∫ ω, f m ω ∂P))
            + ((∫ ω, G ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P) * (∫ ω, f m ω ∂P)‖
        ≤ ‖(∫ ω, G ω * f m ω ∂P) - (∫ ω, G ω ∂P) * (∫ ω, f m ω ∂P)‖
          + ‖((∫ ω, G ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P) * (∫ ω, f m ω ∂P)‖ :=
          norm_add_le _ _
      _ ≤ 16 * K * M m * alphaMixingCoef P Y n
          + (16 * ((m - 1 : ℕ) : ℝ) * alphaMixingCoef P Y n * K) * M m :=
          add_le_add hpair hbound2
      _ = 16 * (m : ℝ) * alphaMixingCoef P Y n * (K * M m) := by
          rw [hcast2]; ring
