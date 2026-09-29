-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_unit_ball_coordinate_flip_stopped_loss_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T10:18:55.544304+00:00
-- url     : https://prove2.me/submissions/dcf60500-813c-459b-9ba1-fe56e5d0b887

import Mathlib
import Definitions.Def_LinearBanditProtocol

open Matrix MeasureTheory ProbabilityTheory

namespace LB24f8

open BanditAlgorithm

variable {d : ℕ}

abbrev Hist (d m : ℕ) := LinearBanditHistory d m

/-- snoc on linear bandit histories -/
abbrev sn {m : ℕ} (h : Hist d m) (y : (Fin d → ℝ) × ℝ) : Hist d (m + 1) :=
  Fin.snoc (α := fun _ ↦ (Fin d → ℝ) × ℝ) h y

lemma lintegral_step (θ : Fin d → ℝ) (π : LinearBanditPolicy d) (m : ℕ)
    {F : Hist d (m + 1) → ENNReal} (hF : Measurable F) :
    ∫⁻ h, F h ∂(linearBanditMeasure θ π (m + 1)) =
      ∫⁻ h, ∫⁻ a, ∫⁻ η, F (sn h (a, a ⬝ᵥ θ + η))
        ∂(gaussianReal 0 1) ∂(π.select m h) ∂(linearBanditMeasure θ π m) := by
  have hm := hF.comp (measurable_linearBanditHistorySnoc θ)
  rw [linearBanditMeasure, lintegral_map hF (measurable_linearBanditHistorySnoc θ),
    Measure.lintegral_compProd (f := fun p : (Hist d m × (Fin d → ℝ)) × ℝ =>
      F (Fin.snoc (α := fun _ ↦ (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.1.2 ⬝ᵥ θ + p.2))) hm]
  simp only [Kernel.const_apply]
  rw [Measure.lintegral_compProd]
  exact hm.lintegral_prod_right'

lemma gauss_shift (G : ℝ → ENNReal) (hG : Measurable G) (μ μ' : ℝ) :
    ∫⁻ η, G (μ + η) ∂(gaussianReal 0 1) =
      ∫⁻ η, G (μ' + η) * ENNReal.ofReal (Real.exp ((μ - μ') * η - (μ - μ') ^ 2 / 2))
        ∂(gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _)
      (g := fun η => G (μ + η)) (hG.comp (measurable_const_add μ)),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _)
      (g := fun η => G (μ' + η) * ENNReal.ofReal (Real.exp ((μ - μ') * η - (μ - μ') ^ 2 / 2)))
      ((hG.comp (measurable_const_add μ')).mul (by fun_prop))]
  have h1 : ∫⁻ a, ((gaussianPDF 0 1) * fun η => G (μ + η)) a =
      ∫⁻ x, gaussianPDF 0 1 (x - μ) * G x := by
    rw [← lintegral_add_left_eq_self (fun x => gaussianPDF 0 1 (x - μ) * G x) μ]
    simp
  have h2 : ∫⁻ a, ((gaussianPDF 0 1) * fun η => G (μ' + η) *
        ENNReal.ofReal (Real.exp ((μ - μ') * η - (μ - μ') ^ 2 / 2))) a =
      ∫⁻ x, gaussianPDF 0 1 (x - μ') * (G x *
        ENNReal.ofReal (Real.exp ((μ - μ') * (x - μ') - (μ - μ') ^ 2 / 2))) := by
    rw [← lintegral_add_left_eq_self (fun x => gaussianPDF 0 1 (x - μ') * (G x *
        ENNReal.ofReal (Real.exp ((μ - μ') * (x - μ') - (μ - μ') ^ 2 / 2)))) μ']
    simp
  rw [h1, h2]
  congr 1
  funext x
  have : gaussianPDF 0 1 (x - μ) = gaussianPDF 0 1 (x - μ') *
      ENNReal.ofReal (Real.exp ((μ - μ') * (x - μ') - (μ - μ') ^ 2 / 2)) := by
    simp only [gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e : Real.exp (-(x - μ - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) =
        Real.exp (-(x - μ' - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) *
        Real.exp ((μ - μ') * (x - μ') - (μ - μ') ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [e, ← mul_assoc]
  rw [this]
  ring

section stop
variable (i : Fin d) (b : ℝ)

noncomputable def psum {m : ℕ} (h : Hist d m) (k : ℕ) : ℝ :=
  ∑ s : Fin m, if (s : ℕ) < k then ((h s).1 i) ^ 2 else 0

noncomputable def stopH {m : ℕ} (h : Hist d m) : Hist d m :=
  fun t => if psum i h t < b then h t else (0, 0)

variable {i b}

lemma psum_zero {m : ℕ} (h : Hist d m) : psum i h 0 = 0 := by
  simp [psum]

lemma psum_mono {m : ℕ} (h : Hist d m) {k k' : ℕ} (hk : k ≤ k') :
    psum i h k ≤ psum i h k' := by
  unfold psum
  apply Finset.sum_le_sum
  intro s _
  split_ifs with h1 h2 h2
  · exact le_rfl
  · omega
  · positivity
  · exact le_rfl

lemma psum_succ {m : ℕ} (h : Hist d m) (k : ℕ) :
    psum i h (k + 1) = psum i h k + (if hk : k < m then ((h ⟨k, hk⟩).1 i) ^ 2 else 0) := by
  unfold psum
  split_ifs with hk
  · have : ∀ s : Fin m, (if (s : ℕ) < k + 1 then ((h s).1 i) ^ 2 else 0) =
        (if (s : ℕ) < k then ((h s).1 i) ^ 2 else 0) +
          (if s = ⟨k, hk⟩ then ((h s).1 i) ^ 2 else 0) := by
      intro s
      by_cases h1 : (s : ℕ) < k
      · have : s ≠ ⟨k, hk⟩ := by intro e; rw [e] at h1; simp at h1
        simp [h1, this, show (s : ℕ) < k + 1 by omega]
      · by_cases h2 : (s : ℕ) = k
        · have : s = ⟨k, hk⟩ := Fin.ext h2
          simp [this]
        · have : s ≠ ⟨k, hk⟩ := by intro e; rw [e] at h2; simp at h2
          simp [h1, this, show ¬ (s : ℕ) < k + 1 by omega]
    rw [Finset.sum_congr rfl (fun s _ => this s), Finset.sum_add_distrib]
    simp
  · simp only [add_zero]
    apply Finset.sum_congr rfl
    intro s _
    have := s.isLt
    rw [if_pos (by omega), if_pos (by omega)]

lemma psum_full {m : ℕ} (h : Hist d m) : psum i h m = ∑ t, ((h t).1 i) ^ 2 := by
  unfold psum
  apply Finset.sum_congr rfl
  intro s _
  rw [if_pos s.isLt]

lemma psum_snoc {m : ℕ} (h : Hist d m) (y : (Fin d → ℝ) × ℝ) (k : ℕ) :
    psum i (sn h y) k = psum i h k + (if m < k then (y.1 i) ^ 2 else 0) := by
  unfold psum
  rw [Fin.sum_univ_castSucc]
  simp [sn, Fin.snoc_castSucc, Fin.snoc_last]

lemma stop_apply_of_lt {m : ℕ} (h : Hist d m) {k : ℕ} (hk : psum i h k < b) (s : Fin m)
    (hs : (s : ℕ) < k) : stopH i b h s = h s := by
  unfold stopH
  rw [if_pos (lt_of_le_of_lt (psum_mono h hs.le) hk)]

lemma psum_stop_of_lt {m : ℕ} (h : Hist d m) {k : ℕ} (hk : psum i h k < b) :
    psum i (stopH i b h) k = psum i h k := by
  unfold psum
  apply Finset.sum_congr rfl
  intro s _
  split_ifs with hs
  · rw [stop_apply_of_lt h hk s hs]
  · rfl

lemma psum_stop_ge {m : ℕ} (h : Hist d m) : ∀ k : ℕ, b ≤ psum i h k → b ≤ psum i (stopH i b h) k
  | 0 => by simp [psum_zero]
  | k + 1 => by
    intro hb
    by_cases hk : psum i h k < b
    · rw [psum_succ, psum_stop_of_lt h hk]
      rw [psum_succ] at hb
      split_ifs with hkm
      · have e : stopH i b h ⟨k, hkm⟩ = h ⟨k, hkm⟩ := by simp only [stopH]; rw [if_pos hk]
        rw [e]
        simpa [hkm] using hb
      · simpa [hkm] using hb
    · push Not at hk
      exact le_trans (psum_stop_ge h k hk) (psum_mono _ (by omega))

lemma psum_stop_lt_iff {m : ℕ} (h : Hist d m) (k : ℕ) :
    psum i (stopH i b h) k < b ↔ psum i h k < b := by
  constructor
  · intro H
    by_contra H2
    push Not at H2
    exact absurd (psum_stop_ge h k H2) (not_le.mpr H)
  · intro H
    rwa [psum_stop_of_lt h H]

lemma stop_stop {m : ℕ} (h : Hist d m) : stopH i b (stopH i b h) = stopH i b h := by
  funext t
  have e : stopH i b (stopH i b h) t =
      if psum i (stopH i b h) t < b then stopH i b h t else (0, 0) := rfl
  rw [e]
  by_cases hc : psum i h t < b
  · rw [if_pos ((psum_stop_lt_iff h t).mpr hc)]
  · rw [if_neg (fun H => hc ((psum_stop_lt_iff h t).mp H))]
    simp [stopH, hc]

lemma stop_eq_self {m : ℕ} (h : Hist d m) (hm : psum i h m < b) : stopH i b h = h := by
  funext t
  exact stop_apply_of_lt h hm t t.isLt

lemma stop_snoc {m : ℕ} (h : Hist d m) (y : (Fin d → ℝ) × ℝ) :
    stopH i b (sn h y) = sn (stopH i b h) (if psum i h m < b then y else (0, 0)) := by
  funext t
  refine Fin.lastCases ?_ (fun s => ?_) t
  · simp only [stopH, sn, Fin.snoc_last, psum_snoc, Fin.val_last, lt_irrefl, if_false, add_zero]
  · simp only [stopH, sn, Fin.snoc_castSucc, psum_snoc, Fin.val_castSucc]
    have : ¬ m < (s : ℕ) := by have := s.isLt; omega
    simp [this]

lemma psum_stop_le {m : ℕ} (h : Hist d m) (hb : 0 ≤ b) (h1 : ∀ t, ((h t).1 i) ^ 2 ≤ 1) :
    ∀ k : ℕ, psum i (stopH i b h) k ≤ b + 1
  | 0 => by rw [psum_zero]; linarith
  | k + 1 => by
    rw [psum_succ]
    split_ifs with hkm
    · by_cases hk : psum i h k < b
      · have e : stopH i b h ⟨k, hkm⟩ = h ⟨k, hkm⟩ := by simp only [stopH]; rw [if_pos hk]
        rw [psum_stop_of_lt h hk, e]
        linarith [h1 ⟨k, hkm⟩]
      · have : stopH i b h ⟨k, hkm⟩ = (0, 0) := by
          simp only [stopH]; rw [if_neg hk]
        rw [this]
        simpa using psum_stop_le h hb h1 k
    · simpa using psum_stop_le h hb h1 k

end stop

section lr
variable (θ θm : Fin d → ℝ)

noncomputable def rho (y : (Fin d → ℝ) × ℝ) : ℝ :=
  Real.exp ((y.1 ⬝ᵥ θ - y.1 ⬝ᵥ θm) * (y.2 - y.1 ⬝ᵥ θm) - (y.1 ⬝ᵥ θ - y.1 ⬝ᵥ θm) ^ 2 / 2)

noncomputable def ell {m : ℕ} (h : Hist d m) : ℝ := ∏ t, rho θ θm (h t)

lemma rho_zero : rho θ θm (0, 0) = 1 := by simp [rho]

lemma ell_snoc {m : ℕ} (h : Hist d m) (y : (Fin d → ℝ) × ℝ) :
    ell θ θm (sn h y) = ell θ θm h * rho θ θm y := by
  simp [ell, Fin.prod_univ_castSucc, sn]

lemma ell_nonneg {m : ℕ} (h : Hist d m) : 0 ≤ ell θ θm h :=
  Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le

lemma measurable_rho : Measurable (rho θ θm) := by
  unfold rho
  simp only [dotProduct]
  fun_prop

lemma measurable_ell {m : ℕ} : Measurable (fun h : Hist d m => ell θ θm h) := by
  unfold ell
  exact Finset.measurable_prod _ fun t _ => (measurable_rho θ θm).comp (measurable_pi_apply t)

end lr

lemma measurable_psum (i : Fin d) {m : ℕ} (k : ℕ) : Measurable (fun h : Hist d m => psum i h k) := by
  unfold psum
  refine Finset.measurable_sum _ fun s _ => ?_
  by_cases hs : (s : ℕ) < k
  · simp only [hs, if_true]; fun_prop
  · simp only [hs, if_false]; fun_prop

lemma measurable_stopH (i : Fin d) (b : ℝ) {m : ℕ} : Measurable (fun h : Hist d m => stopH i b h) := by
  rw [measurable_pi_iff]
  intro t
  exact Measurable.ite (measurableSet_lt (measurable_psum i t) measurable_const)
    (measurable_pi_apply t) measurable_const

lemma measurable_sn {m : ℕ} : Measurable (fun p : Hist d m × ((Fin d → ℝ) × ℝ) => sn p.1 p.2) := by
  rw [measurable_pi_iff]
  intro t
  refine Fin.lastCases ?_ (fun s => ?_) t
  · simp only [sn, Fin.snoc_last]; exact measurable_snd
  · simp only [sn, Fin.snoc_castSucc]; exact (measurable_pi_apply s).comp measurable_fst

lemma change_of_measure (π : LinearBanditPolicy d) (θ θm : Fin d → ℝ) (i : Fin d) (b : ℝ) :
    ∀ (m : ℕ) (F : Hist d m → ENNReal), Measurable F →
      ∫⁻ h, F (stopH i b h) ∂(linearBanditMeasure θ π m) =
        ∫⁻ h, F (stopH i b h) * ENNReal.ofReal (ell θ θm (stopH i b h))
          ∂(linearBanditMeasure θm π m)
  | 0, F, hF => by
    rw [linearBanditMeasure, linearBanditMeasure,
      lintegral_dirac' _ (f := fun h => F (stopH i b h)) (hF.comp (measurable_stopH i b)),
      lintegral_dirac' _ (f := fun h => F (stopH i b h) * ENNReal.ofReal (ell θ θm (stopH i b h)))
        ((hF.comp (measurable_stopH i b)).mul
        (ENNReal.measurable_ofReal.comp ((measurable_ell θ θm).comp (measurable_stopH i b))))]
    simp [ell]
  | m + 1, F, hF => by
    set G : Hist d m → ENNReal := fun h' => if psum i h' m < b then
        ∫⁻ a, ∫⁻ η, F (sn h' (a, a ⬝ᵥ θ + η)) ∂(gaussianReal 0 1) ∂(π.select m h')
      else F (sn h' (0, 0)) with hGdef
    have hG : Measurable G := by
      refine Measurable.ite (measurableSet_lt (measurable_psum i m) measurable_const) ?_ ?_
      · exact Measurable.lintegral_kernel_prod_right' (κ := π.select m)
          (f := fun p : Hist d m × (Fin d → ℝ) =>
            ∫⁻ η, F (sn p.1 (p.2, p.2 ⬝ᵥ θ + η)) ∂(gaussianReal 0 1))
          ((hF.comp (measurable_linearBanditHistorySnoc θ)).lintegral_prod_right')
      · exact hF.comp (measurable_sn.comp (measurable_id.prodMk measurable_const))
    have ih := change_of_measure π θ θm i b m G hG
    have hL : ∫⁻ h, F (stopH i b h) ∂(linearBanditMeasure θ π (m + 1)) =
        ∫⁻ h, G (stopH i b h) ∂(linearBanditMeasure θ π m) := by
      rw [lintegral_step θ π m (F := fun h => F (stopH i b h)) (hF.comp (measurable_stopH i b))]
      apply lintegral_congr
      intro h
      simp only [stop_snoc]
      by_cases hb : psum i h m < b
      · rw [stop_eq_self h hb]
        simp only [hGdef, hb, if_true]
      · have hb' : ¬ psum i (stopH i b h) m < b := fun H => hb ((psum_stop_lt_iff h m).mp H)
        simp only [hGdef, hb, hb', if_false]
        simp [lintegral_const, measure_univ]
    have hR : ∫⁻ h, F (stopH i b h) * ENNReal.ofReal (ell θ θm (stopH i b h))
          ∂(linearBanditMeasure θm π (m + 1)) =
        ∫⁻ h, G (stopH i b h) * ENNReal.ofReal (ell θ θm (stopH i b h))
          ∂(linearBanditMeasure θm π m) := by
      rw [lintegral_step θm π m
        (F := fun h => F (stopH i b h) * ENNReal.ofReal (ell θ θm (stopH i b h)))
        ((hF.comp (measurable_stopH i b)).mul
        (ENNReal.measurable_ofReal.comp ((measurable_ell θ θm).comp (measurable_stopH i b))))]
      apply lintegral_congr
      intro h
      simp only [stop_snoc, ell_snoc]
      by_cases hb : psum i h m < b
      · rw [stop_eq_self h hb]
        simp only [hGdef, hb, if_true]
        rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro a
        rw [gauss_shift (fun x => F (sn h (a, x)))
          (hF.comp (measurable_sn.comp (measurable_const.prodMk
            (measurable_const.prodMk measurable_id)))) (a ⬝ᵥ θ) (a ⬝ᵥ θm)]
        rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro η
        rw [ENNReal.ofReal_mul (ell_nonneg θ θm h), rho]
        have e1 : a ⬝ᵥ θm + η - a ⬝ᵥ θm = η := by ring
        simp only [e1]
        ring
      · have hb' : ¬ psum i (stopH i b h) m < b := fun H => hb ((psum_stop_lt_iff h m).mp H)
        simp only [hGdef, hb, hb', if_false, rho_zero, mul_one]
        simp [lintegral_const, measure_univ]
    rw [hL, hR, ih]


lemma sq_le_dot (a : Fin d → ℝ) (i : Fin d) : (a i) ^ 2 ≤ a ⬝ᵥ a := by
  simp only [dotProduct]
  rw [sq]
  exact Finset.single_le_sum (f := fun j => a j * a j) (fun j _ => mul_self_nonneg (a j))
    (Finset.mem_univ i)

lemma supp_null (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) (θ : Fin d → ℝ)
    (i : Fin d) : ∀ m : ℕ, linearBanditMeasure θ π m {h | ∃ t, 1 < ((h t).1 i) ^ 2} = 0
  | 0 => by
    have : {h : Hist d 0 | ∃ t, 1 < ((h t).1 i) ^ 2} = ∅ := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨t, _⟩
      exact t.elim0
    rw [this, measure_empty]
  | m + 1 => by
    have hms : ∀ k, MeasurableSet {h : Hist d k | ∃ t, 1 < ((h t).1 i) ^ 2} := by
      intro k
      have : {h : Hist d k | ∃ t, 1 < ((h t).1 i) ^ 2} = ⋃ t, {h | 1 < ((h t).1 i) ^ 2} := by
        ext; simp
      rw [this]
      exact MeasurableSet.iUnion fun t => measurableSet_lt measurable_const (by fun_prop)
    have hA : MeasurableSet {a : Fin d → ℝ | 1 < (a i) ^ 2} :=
      measurableSet_lt measurable_const (by fun_prop)
    have ih := supp_null π hsupp θ i m
    apply le_antisymm _ zero_le
    rw [← lintegral_indicator_one (hms (m + 1)),
      lintegral_step θ π m (F := {h : Hist d (m + 1) | ∃ t, 1 < ((h t).1 i) ^ 2}.indicator 1)
        (measurable_one.indicator (hms (m + 1)))]
    have hpt : ∀ (h : Hist d m) (a : Fin d → ℝ) (x : ℝ),
        {h : Hist d (m + 1) | ∃ t, 1 < ((h t).1 i) ^ 2}.indicator 1 (sn h (a, x)) ≤
          {h : Hist d m | ∃ t, 1 < ((h t).1 i) ^ 2}.indicator (1 : Hist d m → ENNReal) h +
            {a : Fin d → ℝ | 1 < (a i) ^ 2}.indicator 1 a := by
      intro h a x
      by_cases hin : sn h (a, x) ∈ {h : Hist d (m + 1) | ∃ t, 1 < ((h t).1 i) ^ 2}
      · rw [Set.indicator_of_mem hin]
        simp only [Pi.one_apply]
        obtain ⟨t, ht⟩ := hin
        revert ht
        refine Fin.lastCases ?_ (fun s => ?_) t
        · intro ht
          simp only [sn, Fin.snoc_last] at ht
          rw [Set.indicator_of_mem (show a ∈ {a : Fin d → ℝ | 1 < (a i) ^ 2} from ht)]
          simp
        · intro ht
          simp only [sn, Fin.snoc_castSucc] at ht
          rw [Set.indicator_of_mem
            (show h ∈ {h : Hist d m | ∃ t, 1 < ((h t).1 i) ^ 2} from ⟨s, ht⟩)]
          simp
      · rw [Set.indicator_of_notMem hin]
        exact zero_le
    calc ∫⁻ h, ∫⁻ a, ∫⁻ η, {h : Hist d (m + 1) | ∃ t, 1 < ((h t).1 i) ^ 2}.indicator 1
            (sn h (a, a ⬝ᵥ θ + η)) ∂(gaussianReal 0 1) ∂(π.select m h) ∂(linearBanditMeasure θ π m)
        ≤ ∫⁻ h, ∫⁻ a, ({h : Hist d m | ∃ t, 1 < ((h t).1 i) ^ 2}.indicator 1 h +
            {a : Fin d → ℝ | 1 < (a i) ^ 2}.indicator 1 a) ∂(π.select m h)
              ∂(linearBanditMeasure θ π m) := by
          apply lintegral_mono
          intro h
          apply lintegral_mono
          intro a
          calc _ ≤ ∫⁻ η, ({h : Hist d m | ∃ t, 1 < ((h t).1 i) ^ 2}.indicator 1 h +
                {a : Fin d → ℝ | 1 < (a i) ^ 2}.indicator 1 a) ∂(gaussianReal 0 1) :=
                lintegral_mono (fun η => hpt h a _)
            _ = _ := by rw [lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ h, ({h : Hist d m | ∃ t, 1 < ((h t).1 i) ^ 2}.indicator 1 h +
            π.select m h {a : Fin d → ℝ | 1 < (a i) ^ 2}) ∂(linearBanditMeasure θ π m) := by
          apply lintegral_congr
          intro h
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_indicator_one hA]
      _ = 0 := by
          have h0 : ∀ h : Hist d m, π.select m h {a : Fin d → ℝ | 1 < (a i) ^ 2} = 0 := by
            intro h
            apply le_antisymm _ zero_le
            calc π.select m h {a : Fin d → ℝ | 1 < (a i) ^ 2}
                ≤ π.select m h {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}ᶜ := by
                  apply measure_mono
                  intro a ha
                  simp only [Set.mem_setOf_eq] at ha
                  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
                  exact lt_of_lt_of_le ha (sq_le_dot a i)
              _ = 0 := hsupp m h
          simp only [h0, add_zero]
          rw [lintegral_indicator_one (hms m), ih]

lemma supp_ae (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) (θ : Fin d → ℝ)
    (i : Fin d) (m : ℕ) : ∀ᵐ h ∂(linearBanditMeasure θ π m), ∀ t, ((h t).1 i) ^ 2 ≤ 1 := by
  rw [ae_iff]
  simpa only [not_forall, not_le] using supp_null π hsupp θ i m


noncomputable def W (i : Fin d) (b x : ℝ) {m : ℕ} (h : Hist d m) : ℝ :=
  ∑ t : Fin m, if psum i h (t : ℕ) < b then (1 / Real.sqrt d - (h t).1 i * x) ^ 2 else 0

lemma W_stop (i : Fin d) (b x : ℝ) {m : ℕ} (h : Hist d m) :
    W i b x (stopH i b h) = W i b x h := by
  unfold W
  apply Finset.sum_congr rfl
  intro t _
  by_cases hc : psum i h t < b
  · rw [if_pos ((psum_stop_lt_iff h t).mpr hc), if_pos hc]
    have e : stopH i b h t = h t := by simp only [stopH]; rw [if_pos hc]
    rw [e]
  · rw [if_neg (fun H => hc ((psum_stop_lt_iff h t).mp H)), if_neg hc]

lemma W_nonneg (i : Fin d) (b x : ℝ) {m : ℕ} (h : Hist d m) : 0 ≤ W i b x h :=
  Finset.sum_nonneg fun t _ => by split_ifs <;> positivity

lemma measurable_W (i : Fin d) (b x : ℝ) {m : ℕ} : Measurable (fun h : Hist d m => W i b x h) := by
  unfold W
  exact Finset.measurable_sum _ fun t _ => Measurable.ite
    (measurableSet_lt (measurable_psum i t) measurable_const) (by fun_prop) measurable_const

lemma W_le (hd : 0 < d) (i : Fin d) (b : ℝ) {x : ℝ} (hx : x ^ 2 = 1) {m : ℕ} (h : Hist d m)
    (h1 : ∀ t, ((h t).1 i) ^ 2 ≤ 1) : W i b x h ≤ 4 * m := by
  unfold W
  have hdd : (1 / Real.sqrt d) ^ 2 ≤ 1 := by
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [div_le_one (by exact_mod_cast hd)]
    exact_mod_cast hd
  calc _ ≤ ∑ _t : Fin m, (4 : ℝ) := Finset.sum_le_sum fun t _ => by
          split_ifs
          · have hv : ((h t).1 i * x) ^ 2 ≤ 1 := by rw [mul_pow, hx, mul_one]; exact h1 t
            nlinarith [sq_nonneg (1 / Real.sqrt d + (h t).1 i * x)]
          · norm_num
    _ = 4 * m := by simp; ring

lemma sum_act_ge (hd : 0 < d) (i : Fin d) {m : ℕ} (h : Hist d m) :
    (m : ℝ) / d ≤ ∑ t : Fin m, if psum i h (t : ℕ) < (m : ℝ) / d then (1 / (d : ℝ) + ((h t).1 i) ^ 2) else 0 := by
  by_cases hall : ∀ t : Fin m, psum i h t < (m : ℝ) / d
  · calc (m : ℝ) / d = ∑ _t : Fin m, (1 / (d : ℝ)) := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum fun t _ => by
          rw [if_pos (hall t)]; nlinarith [sq_nonneg ((h t).1 i)]
  · push Not at hall
    obtain ⟨t0, ht0⟩ := hall
    have h1 : (m : ℝ) / d ≤ psum i h m := le_trans ht0 (psum_mono h t0.isLt.le)
    have h2 := psum_stop_ge h m h1
    rw [psum_full] at h2
    calc (m : ℝ) / d ≤ ∑ t, ((stopH i ((m : ℝ) / d) h t).1 i) ^ 2 := h2
      _ ≤ _ := Finset.sum_le_sum fun t _ => by
          simp only [stopH]
          split_ifs with hc
          · have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
            linarith
          · simp

lemma W_sum (hd : 0 < d) (i : Fin d) {x : ℝ} (hx : x ^ 2 = 1) {m : ℕ} (h : Hist d m) :
    2 * ((m : ℝ) / d) ≤ W i ((m : ℝ) / d) x h + W i ((m : ℝ) / d) (-x) h := by
  unfold W
  rw [← Finset.sum_add_distrib]
  have hu : (1 / Real.sqrt d) ^ 2 = 1 / (d : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have e : ∀ t : Fin m, ((if psum i h t < (m : ℝ) / d then (1 / Real.sqrt d - (h t).1 i * x) ^ 2 else 0) +
      (if psum i h t < (m : ℝ) / d then (1 / Real.sqrt d - (h t).1 i * -x) ^ 2 else 0)) =
      2 * (if psum i h t < (m : ℝ) / d then (1 / (d : ℝ) + ((h t).1 i) ^ 2) else 0) := by
    intro t
    split_ifs
    · linear_combination 2 * hu + 2 * ((h t).1 i) ^ 2 * hx
    · ring
  rw [Finset.sum_congr rfl (fun t _ => e t), ← Finset.mul_sum]
  have := sum_act_ge hd i h
  linarith

lemma rho_mul (θ θ' : Fin d → ℝ) (y : (Fin d → ℝ) × ℝ) :
    rho θ (fun j => (θ j + θ' j) / 2) y * rho θ' (fun j => (θ j + θ' j) / 2) y =
      Real.exp (-((y.1 ⬝ᵥ θ - y.1 ⬝ᵥ θ') ^ 2 / 4)) := by
  have hm : y.1 ⬝ᵥ (fun j => (θ j + θ' j) / 2) = (y.1 ⬝ᵥ θ + y.1 ⬝ᵥ θ') / 2 := by
    simp only [dotProduct]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [rho, rho, ← Real.exp_add, hm]
  congr 1
  ring

lemma ell_mul (θ θ' : Fin d → ℝ) {m : ℕ} (h : Hist d m) :
    ell θ (fun j => (θ j + θ' j) / 2) h * ell θ' (fun j => (θ j + θ' j) / 2) h =
      Real.exp (-(∑ t, ((h t).1 ⬝ᵥ θ - (h t).1 ⬝ᵥ θ') ^ 2 / 4)) := by
  unfold ell
  rw [← Finset.prod_mul_distrib]
  simp only [rho_mul]
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

lemma key_real {F1 F2 L1 L2 c κ : ℝ} (hF1 : 0 ≤ F1) (hF2 : 0 ≤ F2) (hc : c ≤ F1 + F2)
    (hc0 : 0 ≤ c) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) (_hκ : 0 ≤ κ) (hL : κ ^ 2 ≤ L1 * L2) :
    4 * c * κ ≤ 3 * (F1 * L1 + F2 * L2) + c * L1 + c * L2 := by
  rcases le_total L1 L2 with h | h
  · have h1 : c * L1 ≤ F1 * L1 + F2 * L2 := by
      nlinarith [mul_le_mul_of_nonneg_left h hF2, mul_nonneg (sub_nonneg.2 hc) hL1]
    have h3 : (4 * κ) ^ 2 ≤ (4 * L1 + L2) ^ 2 := by nlinarith [sq_nonneg (4 * L1 - L2)]
    have h2 : 4 * κ ≤ 4 * L1 + L2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hc0]
  · have h1 : c * L2 ≤ F1 * L1 + F2 * L2 := by
      nlinarith [mul_le_mul_of_nonneg_left h hF1, mul_nonneg (sub_nonneg.2 hc) hL2]
    have h3 : (4 * κ) ^ 2 ≤ (4 * L2 + L1) ^ 2 := by nlinarith [sq_nonneg (4 * L2 - L1)]
    have h2 : 4 * κ ≤ 4 * L2 + L1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hc0]

lemma ennreal_split {A1 A2 L1 L2 c : ℝ} (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hL1 : 0 ≤ L1)
    (hL2 : 0 ≤ L2) (hc : 0 ≤ c) :
    ENNReal.ofReal (3 * (A1 * L1 + A2 * L2) + c * L1 + c * L2) =
      3 * (ENNReal.ofReal A1 * ENNReal.ofReal L1 + ENNReal.ofReal A2 * ENNReal.ofReal L2) +
        ENNReal.ofReal c * ENNReal.ofReal L1 + ENNReal.ofReal c * ENNReal.ofReal L2 := by
  have p1 := mul_nonneg hA1 hL1
  have p2 := mul_nonneg hA2 hL2
  have p3 := mul_nonneg hc hL1
  have p4 := mul_nonneg hc hL2
  have p5 : 0 ≤ 3 * (A1 * L1 + A2 * L2) := by linarith
  rw [ENNReal.ofReal_add (add_nonneg p5 p3) p4, ENNReal.ofReal_add p5 p3,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_add p1 p2,
    ENNReal.ofReal_mul hA1, ENNReal.ofReal_mul hA2, ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hc,
    ENNReal.ofReal_ofNat]


theorem main_ineq (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    {n : ℕ} (hd : 0 < d) (i : Fin d) (θ θ' : Fin d → ℝ) (Δ x : ℝ) (hx : x ^ 2 = 1)
    (hdiff : ∀ a : Fin d → ℝ, (a ⬝ᵥ θ - a ⬝ᵥ θ') ^ 2 = 4 * Δ ^ 2 * (a i) ^ 2)
    (hΔ : Δ ^ 2 * ((n : ℝ) / d + 1) ≤ 1 / 16) :
    (n : ℝ) / d ≤ ∫ h, W i ((n : ℝ) / d) x h ∂(linearBanditMeasure θ π n) +
      ∫ h, W i ((n : ℝ) / d) (-x) h ∂(linearBanditMeasure θ' π n) := by
  set b : ℝ := (n : ℝ) / d with hb
  have hb0 : 0 ≤ b := by positivity
  set θm : Fin d → ℝ := fun j => (θ j + θ' j) / 2 with hθm
  have hx' : (-x) ^ 2 = 1 := by rw [neg_sq]; exact hx
  have mS := measurable_stopH (m := n) i b
  have mW1 : Measurable (fun h : Hist d n => ENNReal.ofReal (W i b x (stopH i b h))) :=
    ENNReal.measurable_ofReal.comp ((measurable_W i b x).comp mS)
  have mW2 : Measurable (fun h : Hist d n => ENNReal.ofReal (W i b (-x) (stopH i b h))) :=
    ENNReal.measurable_ofReal.comp ((measurable_W i b (-x)).comp mS)
  have mL1 : Measurable (fun h : Hist d n => ENNReal.ofReal (ell θ θm (stopH i b h))) :=
    ENNReal.measurable_ofReal.comp ((measurable_ell θ θm).comp mS)
  have mL2 : Measurable (fun h : Hist d n => ENNReal.ofReal (ell θ' θm (stopH i b h))) :=
    ENNReal.measurable_ofReal.comp ((measurable_ell θ' θm).comp mS)
  -- total masses
  have oneP : ∫⁻ h, ENNReal.ofReal (ell θ θm (stopH i b h)) ∂(linearBanditMeasure θm π n) = 1 := by
    have := change_of_measure π θ θm i b n (fun _ => 1) measurable_const
    simp only [one_mul] at this
    rw [← this, lintegral_const, measure_univ, mul_one]
  have oneQ : ∫⁻ h, ENNReal.ofReal (ell θ' θm (stopH i b h)) ∂(linearBanditMeasure θm π n) = 1 := by
    have := change_of_measure π θ' θm i b n (fun _ => 1) measurable_const
    simp only [one_mul] at this
    rw [← this, lintegral_const, measure_univ, mul_one]
  -- integrability and real integrals
  have intW : ∀ (θ0 : Fin d → ℝ) (y : ℝ), y ^ 2 = 1 →
      Integrable (fun h => W i b y h) (linearBanditMeasure θ0 π n) := by
    intro θ0 y hy
    refine Integrable.mono' (integrable_const ((4 : ℝ) * n))
      (measurable_W i b y).aestronglyMeasurable ?_
    filter_upwards [supp_ae π hsupp θ0 i n] with h hh
    rw [Real.norm_of_nonneg (W_nonneg i b y h)]
    exact W_le hd i b hy h hh
  have hEP : ∫⁻ h, ENNReal.ofReal (W i b x (stopH i b h)) * ENNReal.ofReal (ell θ θm (stopH i b h))
        ∂(linearBanditMeasure θm π n) =
      ENNReal.ofReal (∫ h, W i b x h ∂(linearBanditMeasure θ π n)) := by
    have c := change_of_measure π θ θm i b n (fun h => ENNReal.ofReal (W i b x h))
      (ENNReal.measurable_ofReal.comp (measurable_W i b x))
    rw [← c, ofReal_integral_eq_lintegral_ofReal (intW θ x hx) (ae_of_all _ (W_nonneg i b x))]
    simp only [W_stop]
  have hEQ : ∫⁻ h, ENNReal.ofReal (W i b (-x) (stopH i b h)) *
        ENNReal.ofReal (ell θ' θm (stopH i b h)) ∂(linearBanditMeasure θm π n) =
      ENNReal.ofReal (∫ h, W i b (-x) h ∂(linearBanditMeasure θ' π n)) := by
    have c := change_of_measure π θ' θm i b n (fun h => ENNReal.ofReal (W i b (-x) h))
      (ENNReal.measurable_ofReal.comp (measurable_W i b (-x)))
    rw [← c, ofReal_integral_eq_lintegral_ofReal (intW θ' (-x) hx')
      (ae_of_all _ (W_nonneg i b (-x)))]
    simp only [W_stop]
  -- pointwise inequality
  have hpt : ∀ᵐ h ∂(linearBanditMeasure θm π n),
      ENNReal.ofReal (4 * (2 * b) * (7 / 8)) ≤
        3 * (ENNReal.ofReal (W i b x (stopH i b h)) * ENNReal.ofReal (ell θ θm (stopH i b h)) +
          ENNReal.ofReal (W i b (-x) (stopH i b h)) * ENNReal.ofReal (ell θ' θm (stopH i b h))) +
        ENNReal.ofReal (2 * b) * ENNReal.ofReal (ell θ θm (stopH i b h)) +
        ENNReal.ofReal (2 * b) * ENNReal.ofReal (ell θ' θm (stopH i b h)) := by
    filter_upwards [supp_ae π hsupp θm i n] with h hh
    have hS : ∑ t, ((stopH i b h t).1 i) ^ 2 ≤ b + 1 := by
      rw [← psum_full]; exact psum_stop_le h hb0 hh n
    have hLL : (7 / 8 : ℝ) ^ 2 ≤ ell θ θm (stopH i b h) * ell θ' θm (stopH i b h) := by
      rw [hθm, ell_mul]
      have e : ∑ t, ((stopH i b h t).1 ⬝ᵥ θ - (stopH i b h t).1 ⬝ᵥ θ') ^ 2 / 4 =
          Δ ^ 2 * ∑ t, ((stopH i b h t).1 i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        rw [hdiff]
        ring
      rw [e]
      have hD : Δ ^ 2 * ∑ t, ((stopH i b h t).1 i) ^ 2 ≤ 1 / 16 :=
        le_trans (mul_le_mul_of_nonneg_left hS (sq_nonneg Δ)) hΔ
      have := Real.add_one_le_exp (-(Δ ^ 2 * ∑ t, ((stopH i b h t).1 i) ^ 2))
      nlinarith
    have hsum := W_sum hd i hx (stopH i b h)
    have kr := key_real (W_nonneg i b x (stopH i b h)) (W_nonneg i b (-x) (stopH i b h)) hsum
      (by positivity) (ell_nonneg θ θm _) (ell_nonneg θ' θm _) (by norm_num) hLL
    rw [← ennreal_split (W_nonneg i b x _) (W_nonneg i b (-x) _) (ell_nonneg θ θm _)
      (ell_nonneg θ' θm _) (by positivity)]
    exact ENNReal.ofReal_le_ofReal kr
  -- integrate
  set IP := ∫ h, W i b x h ∂(linearBanditMeasure θ π n)
  set IQ := ∫ h, W i b (-x) h ∂(linearBanditMeasure θ' π n)
  have hIP : 0 ≤ IP := integral_nonneg (W_nonneg i b x)
  have hIQ : 0 ≤ IQ := integral_nonneg (W_nonneg i b (-x))
  have H : ENNReal.ofReal (4 * (2 * b) * (7 / 8)) ≤
      3 * (ENNReal.ofReal IP + ENNReal.ofReal IQ) + ENNReal.ofReal (2 * b) * 1 +
        ENNReal.ofReal (2 * b) * 1 := by
    calc ENNReal.ofReal (4 * (2 * b) * (7 / 8))
        = ∫⁻ _h, ENNReal.ofReal (4 * (2 * b) * (7 / 8)) ∂(linearBanditMeasure θm π n) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := lintegral_mono_ae hpt
      _ = 3 * (ENNReal.ofReal IP + ENNReal.ofReal IQ) + ENNReal.ofReal (2 * b) * 1 +
            ENNReal.ofReal (2 * b) * 1 := by
          rw [lintegral_add_left (((mW1.mul mL1).add (mW2.mul mL2)).const_mul 3 |>.add
              (mL1.const_mul _)),
            lintegral_add_left (((mW1.mul mL1).add (mW2.mul mL2)).const_mul 3),
            lintegral_const_mul _ ((mW1.mul mL1).add (mW2.mul mL2)),
            lintegral_add_left (mW1.mul mL1),
            lintegral_const_mul _ mL1, lintegral_const_mul _ mL2, hEP, hEQ, oneP, oneQ]
  have H' : ENNReal.ofReal (4 * (2 * b) * (7 / 8)) ≤ ENNReal.ofReal (3 * (IP + IQ) + 2 * b + 2 * b) := by
    refine H.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_add hIP hIQ,
      ENNReal.ofReal_ofNat, mul_one]
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp H'
  linarith


end LB24f8

set_option maxHeartbeats 4000000 in
open Matrix MeasureTheory in
theorem solution
    {d n : ℕ} (hd : 0 < d) (hdn : d ≤ 2 * n)
    (π : BanditAlgorithm.LinearBanditPolicy d)
    (hsupp : BanditAlgorithm.IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) (i : Fin d) :
    let Δ := Real.sqrt ((d : ℝ) / (48 * n))
    let sign : Fin d → ℝ := fun j ↦ if σ j then 1 else -1
    let θ : Fin d → ℝ := fun j ↦ Δ * sign j
    let σ' : Fin d → Bool := Function.update σ i (!(σ i))
    let sign' : Fin d → ℝ := fun j ↦ if σ' j then 1 else -1
    let θ' : Fin d → ℝ := fun j ↦ Δ * sign' j
    let active : BanditAlgorithm.LinearBanditHistory d n → Fin n → Prop := fun h t ↦
      (∑ s ∈ Finset.univ.filter (fun s : Fin n ↦ s < t),
          ((h s).1 i) ^ 2) < (n : ℝ) / d
    let U : BanditAlgorithm.LinearBanditHistory d n → ℝ → ℝ := fun h x ↦
      ∑ t, if active h t then
        (1 / Real.sqrt d - (h t).1 i * x) ^ 2 else 0
    (n : ℝ) / d ≤
      (∫ h, U h (sign i) ∂BanditAlgorithm.linearBanditMeasure θ π n) +
      ∫ h, U h (sign' i) ∂BanditAlgorithm.linearBanditMeasure θ' π n := by
  intro Δ sign θ σ' sign' θ' active U
  have hn : 0 < n := by omega
  have hsi : sign i ^ 2 = 1 := by simp only [sign]; split_ifs <;> norm_num
  have hs' : sign' i = -sign i := by
    simp only [sign', sign, σ', Function.update_self]
    cases σ i <;> simp
  have hdiffj : ∀ j, θ j - θ' j = if j = i then 2 * Δ * sign i else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [θ, θ', if_true]
      rw [hs']
      ring
    · simp only [θ, θ', sign', sign, σ', Function.update_of_ne hj, hj, if_false]
      ring
  have hdiff : ∀ a : Fin d → ℝ, (a ⬝ᵥ θ - a ⬝ᵥ θ') ^ 2 = 4 * Δ ^ 2 * (a i) ^ 2 := by
    intro a
    have e : a ⬝ᵥ θ - a ⬝ᵥ θ' = a i * (2 * Δ * sign i) := by
      rw [← dotProduct_sub]
      simp only [dotProduct, Pi.sub_apply, hdiffj, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [e, mul_pow, mul_pow, mul_pow, hsi]
    ring
  have hΔ : Δ ^ 2 * ((n : ℝ) / d + 1) ≤ 1 / 16 := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hdn' : (d : ℝ) ≤ 2 * n := by exact_mod_cast hdn
    simp only [Δ]
    rw [Real.sq_sqrt (by positivity), div_add_one hd'.ne', div_mul_div_comm,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hdn' hd'.le]
  have key := LB24f8.main_ineq π hsupp hd i θ θ' Δ (sign i) hsi hdiff hΔ
  have hU : ∀ h y, U h y = LB24f8.W i ((n : ℝ) / d) y h := by
    intro h y
    simp only [U, active, LB24f8.W, LB24f8.psum, Finset.sum_filter, Fin.lt_def]
    rfl
  simp only [hU, hs']
  exact key
