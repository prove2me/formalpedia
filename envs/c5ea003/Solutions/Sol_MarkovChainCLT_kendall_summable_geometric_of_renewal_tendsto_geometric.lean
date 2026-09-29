-- Prove2me | solution 1 for MarkovChainCLT.kendall_summable_geometric_of_renewal_tendsto_geometric
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T02:51:44.861719+00:00
-- url     : https://prove2.me/submissions/549cb19b-30aa-48a0-b99a-3426dd38eb65

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness

set_option maxHeartbeats 2000000

open Filter Finset
open scoped Topology BigOperators NNReal ENNReal

namespace KendallScratch

/-! ### Elementary facts about the renewal sequence -/

section elementary

variable (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha_zero : a 0 = 0) (hsum : HasSum a 1)
  (v : ℕ → ℝ) (hv0 : v 0 = 1)
  (hv : ∀ n : ℕ, v (n + 1) = ∑ j ∈ Finset.range (n + 1), a (j + 1) * v (n - j))

include ha0 hsum in
lemma a_le_one (k : ℕ) : a k ≤ 1 :=
  le_hasSum hsum k (fun j _ => ha0 j)

include ha0 ha_zero hsum hv0 hv in
lemma v_nonneg_le_one : ∀ n, 0 ≤ v n ∧ v n ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · rw [hv0]; exact ⟨zero_le_one, le_rfl⟩
    · rw [hv m]
      constructor
      · exact Finset.sum_nonneg (fun j hj => mul_nonneg (ha0 _)
          (ih (m - j) (by have := Finset.mem_range.1 hj; omega)).1)
      · calc ∑ j ∈ Finset.range (m + 1), a (j + 1) * v (m - j)
            ≤ ∑ j ∈ Finset.range (m + 1), a (j + 1) := by
              refine Finset.sum_le_sum (fun j hj => ?_)
              have hj' := Finset.mem_range.1 hj
              exact mul_le_of_le_one_right (ha0 _) (ih (m - j) (by omega)).2
          _ = ∑ j ∈ Finset.range (m + 2), a j := by
              rw [Finset.sum_range_succ' (fun j => a j) (m + 1), ha_zero, add_zero]
          _ ≤ 1 := sum_le_hasSum _ (fun j _ => ha0 j) hsum

end elementary

/-! ### The generating functions -/

section series

variable (a : ℕ → ℝ) (v : ℕ → ℝ) (vlim : ℝ)

/-- `A(z) = ∑ aₖ zᵏ`. -/
noncomputable def Aser (z : ℂ) : ℂ := ∑' k, (a k : ℂ) * z ^ k

/-- `V(z) = ∑ vₙ zⁿ`. -/
noncomputable def Vser (z : ℂ) : ℂ := ∑' n, (v n : ℂ) * z ^ n

/-- `H(z) = ∑ (vₙ - v∞) zⁿ`. -/
noncomputable def Hser (z : ℂ) : ℂ := ∑' n, ((v n - vlim : ℝ) : ℂ) * z ^ n

/-- `G(z) = v∞ + (1 - z) H(z)`. -/
noncomputable def Gfun (z : ℂ) : ℂ := (vlim : ℂ) + (1 - z) * Hser v vlim z

end series

section identities

variable {a : ℕ → ℝ} (ha0 : ∀ k, 0 ≤ a k) (ha_zero : a 0 = 0) (hsum : HasSum a 1)
  {v : ℕ → ℝ} (hv0 : v 0 = 1)
  (hv : ∀ n : ℕ, v (n + 1) = ∑ j ∈ Finset.range (n + 1), a (j + 1) * v (n - j))

include ha0 hsum in
lemma summable_norm_A_term {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun k => ‖(a k : ℂ) * z ^ k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hsum.summable
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 k)]
  exact mul_le_of_le_one_right (ha0 k) (pow_le_one₀ (norm_nonneg _) hz)

include ha0 hsum in
lemma norm_Aser_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖Aser a z‖ ≤ 1 := by
  unfold Aser
  refine (norm_tsum_le_tsum_norm (summable_norm_A_term ha0 hsum hz)).trans ?_
  calc ∑' k, ‖(a k : ℂ) * z ^ k‖ ≤ ∑' k, a k := by
        refine Summable.tsum_le_tsum (fun k => ?_) (summable_norm_A_term ha0 hsum hz) hsum.summable
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 k)]
        exact mul_le_of_le_one_right (ha0 k) (pow_le_one₀ (norm_nonneg _) hz)
    _ = 1 := hsum.tsum_eq

include ha0 ha_zero hsum hv0 hv in
lemma summable_norm_V_term {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => ‖(v n : ℂ) * z ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg z) hz)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (v_nonneg_le_one a ha0 ha_zero hsum v hv0 hv n).1]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _)
    (v_nonneg_le_one a ha0 ha_zero hsum v hv0 hv n).2

include ha0 ha_zero hsum hv0 hv in
/-- the renewal equation as an identity of generating functions: `(1 - A) V = 1`. -/
lemma one_sub_Aser_mul_Vser {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - Aser a z) * Vser v z = 1 := by
  have hA := summable_norm_A_term ha0 hsum hz.le
  have hV := summable_norm_V_term ha0 ha_zero hsum hv0 hv hz
  have hprod : Aser a z * Vser v z = ∑' n, ∑ k ∈ range (n + 1), ((a k : ℂ) * z ^ k) * ((v (n - k) : ℂ) * z ^ (n - k)) :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hA hV
  have hterm : ∀ n, (∑ k ∈ range (n + 1), ((a k : ℂ) * z ^ k) * ((v (n - k) : ℂ) * z ^ (n - k)))
      = (if n = 0 then 0 else (v n : ℂ) * z ^ n) := by
    intro n
    have hpow : ∀ k ∈ range (n + 1), ((a k : ℂ) * z ^ k) * ((v (n - k) : ℂ) * z ^ (n - k))
        = ((a k * v (n - k) : ℝ) : ℂ) * z ^ n := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have : z ^ k * z ^ (n - k) = z ^ n := by rw [← pow_add]; congr 1; omega
      push_cast
      calc (a k : ℂ) * z ^ k * ((v (n - k) : ℂ) * z ^ (n - k))
          = (a k : ℂ) * (v (n - k) : ℂ) * (z ^ k * z ^ (n - k)) := by ring
        _ = (a k : ℂ) * (v (n - k) : ℂ) * z ^ n := by rw [this]
    rw [Finset.sum_congr rfl hpow, ← Finset.sum_mul]
    rcases n with _ | m
    · simp [ha_zero]
    · simp only [Nat.succ_ne_zero, if_false]
      congr 1
      rw [Finset.sum_range_succ' (fun k => ((a k * v (m + 1 - k) : ℝ) : ℂ)) (m + 1)]
      simp only [ha_zero, zero_mul, Complex.ofReal_zero, add_zero]
      rw [hv m]
      push_cast
      rfl
  have hif : Summable (fun n : ℕ => if n = 0 then (0:ℂ) else (v n : ℂ) * z ^ n) := by
    refine Summable.of_norm_bounded hV (fun n => ?_)
    split_ifs <;> simp <;> positivity
  rw [sub_mul, one_mul, hprod, tsum_congr hterm, hif.tsum_eq_zero_add]
  simp only [if_true, Nat.succ_ne_zero, if_false, zero_add]
  unfold Vser
  rw [hV.of_norm.tsum_eq_zero_add, hv0]
  simp

end identities

/-! ### Analytic continuation of `G` -/

section analytic

variable {a : ℕ → ℝ} (ha0 : ∀ k, 0 ≤ a k) (ha_zero : a 0 = 0) (hsum : HasSum a 1)
  {v : ℕ → ℝ} (hv0 : v 0 = 1)
  (hv : ∀ n : ℕ, v (n + 1) = ∑ j ∈ Finset.range (n + 1), a (j + 1) * v (n - j))
  {vlim M ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
  (hconv : ∀ n : ℕ, |v n - vlim| ≤ M * ρ ^ n)

/-- the formal power series of `H`. -/
noncomputable def pH (v : ℕ → ℝ) (vlim : ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => ((v n - vlim : ℝ) : ℂ))

lemma pH_sum_eq (v : ℕ → ℝ) (vlim : ℝ) (z : ℂ) : (pH v vlim).sum z = Hser v vlim z := by
  unfold FormalMultilinearSeries.sum pH Hser
  refine tsum_congr (fun n => ?_)
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

lemma norm_pH (v : ℕ → ℝ) (vlim : ℝ) (n : ℕ) : ‖pH v vlim n‖ = |v n - vlim| := by
  unfold pH
  rw [FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs]

include hρ0 hconv in
/-- the radius of `H` is at least `1/ρ'` for every `ρ' > ρ`. -/
lemma le_radius_pH {R₀ : ℝ≥0} (hR₀ : (R₀ : ℝ) * ρ ≤ 1) : (R₀ : ℝ≥0∞) ≤ (pH v vlim).radius := by
  refine (pH v vlim).le_radius_of_bound M (fun n => ?_)
  rw [norm_pH]
  calc |v n - vlim| * (R₀ : ℝ) ^ n ≤ M * ρ ^ n * (R₀ : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (hconv n) (pow_nonneg R₀.2 n)
    _ = M * (ρ * R₀) ^ n := by rw [mul_pow]; ring
    _ ≤ M * 1 := by
        have hM : 0 ≤ M := by
          have := hconv 0
          simp only [pow_zero, mul_one] at this
          exact (abs_nonneg _).trans this
        refine mul_le_mul_of_nonneg_left (pow_le_one₀ (mul_nonneg hρ0 R₀.2) ?_) hM
        rw [mul_comm]; exact hR₀
    _ = M := mul_one M

include hρ0 hconv in
lemma differentiableOn_Hser {R₀ : ℝ≥0} (hR₀ : (R₀ : ℝ) * ρ ≤ 1) (hR₀pos : 0 < R₀) :
    DifferentiableOn ℂ (Hser v vlim) (Metric.ball (0 : ℂ) R₀) := by
  have hrad := le_radius_pH hρ0 hconv (v := v) (vlim := vlim) hR₀
  have hpos : 0 < (pH v vlim).radius := lt_of_lt_of_le (by exact_mod_cast hR₀pos) hrad
  have hdiff := ((pH v vlim).hasFPowerSeriesOnBall hpos).differentiableOn
  have hfun : Hser v vlim = (pH v vlim).sum := funext (fun z => (pH_sum_eq v vlim z).symm)
  rw [hfun]
  refine hdiff.mono ?_
  intro z hz
  have hz' : z ∈ Metric.eball (0 : ℂ) (R₀ : ℝ≥0∞) := by rwa [Metric.emetric_ball_nnreal]
  exact Metric.eball_subset_eball hrad hz'

include hρ0 hconv in
lemma differentiableOn_Gfun {R₀ : ℝ≥0} (hR₀ : (R₀ : ℝ) * ρ ≤ 1) (hR₀pos : 0 < R₀) :
    DifferentiableOn ℂ (Gfun v vlim) (Metric.ball (0 : ℂ) R₀) := by
  unfold Gfun
  exact (differentiableOn_const _).add
    (((differentiableOn_const (1 : ℂ)).sub differentiableOn_id).mul
      (differentiableOn_Hser hρ0 hconv hR₀ hR₀pos))

include ha0 ha_zero hsum hv0 hv hρ0 hρ1 hconv in
/-- the key identity `G(z) (1 - A(z)) = 1 - z` on the open unit disc. -/
lemma Gfun_mul_one_sub_Aser {z : ℂ} (hz : ‖z‖ < 1) :
    Gfun v vlim z * (1 - Aser a z) = 1 - z := by
  have hV := summable_norm_V_term ha0 ha_zero hsum hv0 hv hz
  have hgeo : Summable (fun n : ℕ => (vlim : ℂ) * z ^ n) :=
    (summable_geometric_of_norm_lt_one hz).mul_left _
  have hH : Hser v vlim z = Vser v z - (vlim : ℂ) * (1 - z)⁻¹ := by
    unfold Hser Vser
    have : (fun n : ℕ => ((v n - vlim : ℝ) : ℂ) * z ^ n)
        = fun n => (v n : ℂ) * z ^ n - (vlim : ℂ) * z ^ n := by
      funext n; push_cast; ring
    rw [this, hV.of_norm.tsum_sub hgeo, tsum_mul_left, tsum_geometric_of_norm_lt_one hz]
  have hz1 : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  have hG : Gfun v vlim z = (1 - z) * Vser v z := by
    unfold Gfun
    rw [hH]
    field_simp
    ring
  rw [hG, mul_assoc, mul_comm (Vser v z), one_sub_Aser_mul_Vser ha0 ha_zero hsum hv0 hv hz, mul_one]

end analytic

/-! ### `G` has no zero on the closed unit disc, hence on a larger disc -/

section nonvanishing

variable {a : ℕ → ℝ} (ha0 : ∀ k, 0 ≤ a k) (ha_zero : a 0 = 0) (hsum : HasSum a 1)
  {v : ℕ → ℝ} (hv0 : v 0 = 1)
  (hv : ∀ n : ℕ, v (n + 1) = ∑ j ∈ Finset.range (n + 1), a (j + 1) * v (n - j))
  {vlim M ρ : ℝ} (hvlim : 0 < vlim) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
  (hconv : ∀ n : ℕ, |v n - vlim| ≤ M * ρ ^ n)

include ha0 ha_zero hsum hv0 hv hρ0 hρ1 hconv in
lemma Gfun_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : Gfun v vlim z ≠ 0 := by
  intro h
  have key := Gfun_mul_one_sub_Aser ha0 ha_zero hsum hv0 hv hρ0 hρ1 hconv hz
  rw [h, zero_mul] at key
  have hz1 : z = 1 := by linear_combination key
  rw [hz1, norm_one] at hz
  exact lt_irrefl _ hz

lemma Gfun_one (v : ℕ → ℝ) (vlim : ℝ) : Gfun v vlim 1 = vlim := by
  unfold Gfun; simp

include ha0 ha_zero hsum hv0 hv hvlim hρ0 hρ1 hconv in
lemma Gfun_ne_zero_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1)
    (hcont : ContinuousAt (Gfun v vlim) z) : Gfun v vlim z ≠ 0 := by
  by_cases hz1 : z = 1
  · rw [hz1, Gfun_one]
    exact_mod_cast hvlim.ne'
  intro h0
  have hd : 0 < ‖(1 : ℂ) - z‖ := by
    rw [norm_pos_iff]
    intro h; apply hz1; linear_combination -h
  set ε := ‖(1 : ℂ) - z‖ / 4 with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hcont ε hεpos
  set t := min (δ / 2) (min (‖(1 : ℂ) - z‖ / 2) (1 / 2)) with ht
  have ht0 : 0 < t := by positivity
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htd : t ≤ ‖(1 : ℂ) - z‖ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have ht1 : t ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set y : ℂ := ((1 - t : ℝ) : ℂ) * z with hy
  have hyz : ‖z - y‖ = t := by
    rw [hy]
    have : z - ((1 - t : ℝ) : ℂ) * z = ((t : ℝ) : ℂ) * z := by push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, hz, mul_one]
  have hyn : ‖y‖ < 1 := by
    rw [hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one, abs_of_nonneg (by linarith)]
    linarith
  have hGy : ‖Gfun v vlim y‖ < ε := by
    have := hδG (show dist y z < δ by rw [dist_eq_norm, ← norm_neg, neg_sub, hyz]; exact htδ)
    rwa [dist_eq_norm, h0, sub_zero] at this
  have hkey := Gfun_mul_one_sub_Aser ha0 ha_zero hsum hv0 hv hρ0 hρ1 hconv hyn
  have hA2 : ‖(1 : ℂ) - Aser a y‖ ≤ 2 := by
    calc ‖(1 : ℂ) - Aser a y‖ ≤ ‖(1 : ℂ)‖ + ‖Aser a y‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith [norm_Aser_le_one ha0 hsum hyn.le]
      _ = 2 := by norm_num
  have h1y : ‖(1 : ℂ) - y‖ < 2 * ε := by
    calc ‖(1 : ℂ) - y‖ = ‖Gfun v vlim y * (1 - Aser a y)‖ := by rw [hkey]
      _ = ‖Gfun v vlim y‖ * ‖(1 : ℂ) - Aser a y‖ := norm_mul _ _
      _ ≤ ‖Gfun v vlim y‖ * 2 := mul_le_mul_of_nonneg_left hA2 (norm_nonneg _)
      _ < ε * 2 := by
          exact mul_lt_mul_of_pos_right hGy (by norm_num)
      _ = 2 * ε := by ring
  have h1y' : ‖(1 : ℂ) - z‖ / 2 ≤ ‖(1 : ℂ) - y‖ := by
    have := norm_sub_le ((1 : ℂ) - y) (z - y)
    have heq : (1 : ℂ) - y - (z - y) = 1 - z := by ring
    rw [heq, hyz] at this
    linarith
  rw [hε] at h1y
  linarith

/-- if `G` is continuous on a ball of radius `R₀ > 1` and has no zero on the closed unit disc,
it has no zero on a slightly larger disc. -/
lemma exists_radius_ne_zero (G : ℂ → ℂ) {R₀ : ℝ} (hR₀ : 1 < R₀)
    (hG : ContinuousOn G (Metric.ball (0 : ℂ) R₀)) (hne : ∀ z : ℂ, ‖z‖ ≤ 1 → G z ≠ 0) :
    ∃ r₁ : ℝ, 1 < r₁ ∧ r₁ < R₀ ∧ ∀ z : ℂ, ‖z‖ < r₁ → G z ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  set R' := (1 + R₀) / 2 with hR'
  have hR'1 : 1 < R' := by rw [hR']; linarith
  have hR'0 : R' < R₀ := by rw [hR']; linarith
  have hr : ∀ n : ℕ, 1 < 1 + (R' - 1) / (n + 1) ∧ 1 + (R' - 1) / (n + 1) < R₀ := by
    intro n
    have hpos : 0 < (R' - 1) / (n + 1) := by
      apply div_pos <;> linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hle : (R' - 1) / (n + 1) ≤ R' - 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    constructor <;> linarith
  choose z hz using fun n => hcon _ (hr n).1 (hr n).2
  have hzmem : ∀ n, z n ∈ Metric.closedBall (0 : ℂ) R' := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have hle : (R' - 1) / (n + 1) ≤ R' - 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith [(hz n).1]
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) R').tendsto_subseq hzmem
  -- `‖w‖ ≤ 1`
  have hbound : Tendsto (fun n : ℕ => 1 + (R' - 1) / ((φ n : ℕ) + 1 : ℝ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (R' - 1) / ((φ n : ℕ) + 1 : ℝ)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => ((φ n : ℕ) + 1 : ℝ)) atTop atTop := by
        refine tendsto_atTop_add_const_right _ _ ?_
        exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
      exact tendsto_const_nhds.div_atTop h2
    simpa using tendsto_const_nhds.add h1
  have hwn : ‖w‖ ≤ 1 := by
    have hnorm : Tendsto (fun n => ‖z (φ n)‖) atTop (𝓝 ‖w‖) := (continuous_norm.tendsto w).comp hlim
    exact le_of_tendsto_of_tendsto hnorm hbound
      (Filter.Eventually.of_forall (fun n => (hz (φ n)).1.le))
  -- `G w = 0`
  have hwball : w ∈ Metric.ball (0 : ℂ) R₀ := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hcont : ContinuousAt G w := hG.continuousAt (Metric.isOpen_ball.mem_nhds hwball)
  have hGlim : Tendsto (fun n => G (z (φ n))) atTop (𝓝 (G w)) := hcont.tendsto.comp hlim
  have hzero : Tendsto (fun n => G (z (φ n))) atTop (𝓝 0) := by
    have : (fun n => G (z (φ n))) = fun _ => (0 : ℂ) := funext (fun n => (hz (φ n)).2)
    rw [this]; exact tendsto_const_nhds
  exact hne w hwn (tendsto_nhds_unique hGlim hzero)

end nonvanishing

/-! ### Conclusion -/

section conclusion

/-- the formal power series of `A`. -/
noncomputable def pA (a : ℕ → ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun k => (a k : ℂ))

lemma pA_sum_eq (a : ℕ → ℝ) (z : ℂ) : (pA a).sum z = Aser a z := by
  unfold FormalMultilinearSeries.sum pA Aser
  refine tsum_congr (fun n => ?_)
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

lemma norm_pA (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (n : ℕ) : ‖pA a n‖ = a n := by
  unfold pA
  rw [FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ha0 n)]

theorem kendall_main
    (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha_zero : a 0 = 0) (hsum : HasSum a 1)
    (v : ℕ → ℝ) (hv0 : v 0 = 1)
    (hv : ∀ n : ℕ, v (n + 1) = ∑ j ∈ Finset.range (n + 1), a (j + 1) * v (n - j))
    (vlim M ρ : ℝ) (hvlim : 0 < vlim) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hconv : ∀ n : ℕ, |v n - vlim| ≤ M * ρ ^ n) :
    ∃ κ : ℝ, 1 < κ ∧ Summable (fun k : ℕ => a k * κ ^ k) := by
  -- replace `ρ` by `ρ' ∈ (0,1)`
  have hM : 0 ≤ M := by
    have := hconv 0
    simp only [pow_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  set ρ' := (1 + ρ) / 2 with hρ'
  have hρ'0 : 0 < ρ' := by rw [hρ']; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  have hρρ' : ρ ≤ ρ' := by rw [hρ']; linarith
  have hconv' : ∀ n : ℕ, |v n - vlim| ≤ M * ρ' ^ n := fun n =>
    (hconv n).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρρ' n) hM)
  -- the disc of analyticity of `G`
  set R₀ : ℝ≥0 := ⟨1 / ρ', by positivity⟩ with hR₀
  have hR₀ρ : (R₀ : ℝ) * ρ' ≤ 1 := by
    show (1 / ρ') * ρ' ≤ 1
    rw [one_div, inv_mul_cancel₀ hρ'0.ne']
  have hR₀1 : (1 : ℝ) < R₀ := by
    show (1 : ℝ) < 1 / ρ'
    exact (one_lt_div hρ'0).2 (by linarith)
  have hR₀pos : 0 < R₀ := by
    have : (0 : ℝ) < R₀ := by linarith
    exact_mod_cast this
  have hG : DifferentiableOn ℂ (Gfun v vlim) (Metric.ball (0 : ℂ) R₀) :=
    differentiableOn_Gfun hρ'0.le hconv' hR₀ρ hR₀pos
  -- no zeros on the closed unit disc
  have hne : ∀ z : ℂ, ‖z‖ ≤ 1 → Gfun v vlim z ≠ 0 := by
    intro z hz
    rcases lt_or_eq_of_le hz with hz | hz
    · exact Gfun_ne_zero_of_norm_lt_one ha0 ha_zero hsum hv0 hv hρ'0.le hρ'1 hconv' hz
    · have hzball : z ∈ Metric.ball (0 : ℂ) R₀ := by
        rw [Metric.mem_ball, dist_zero_right, hz]; exact hR₀1
      exact Gfun_ne_zero_of_norm_eq_one ha0 ha_zero hsum hv0 hv hvlim hρ'0.le hρ'1 hconv' hz
        (hG.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hzball))
  obtain ⟨r₁, hr₁, hr₁R, hr₁ne⟩ :=
    exists_radius_ne_zero (Gfun v vlim) hR₀1 hG.continuousOn hne
  -- the analytic continuation `F` of `A`
  set R : ℝ≥0 := ⟨(1 + r₁) / 2, by positivity⟩ with hR
  have hR1 : (1 : ℝ) < R := by show (1 : ℝ) < (1 + r₁) / 2; linarith
  have hRr₁ : (R : ℝ) < r₁ := by show (1 + r₁) / 2 < r₁; linarith
  have hRpos : 0 < R := by
    have : (0 : ℝ) < R := by linarith
    exact_mod_cast this
  set F : ℂ → ℂ := fun z => 1 - (1 - z) / Gfun v vlim z with hF
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) R₀ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hFd : DifferentiableOn ℂ F (Metric.closedBall (0 : ℂ) R) := by
    refine (differentiableOn_const _).sub
      (((differentiableOn_const (1 : ℂ)).sub differentiableOn_id).div (hG.mono hsub) ?_)
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hr₁ne z (by linarith)
  have hFps : HasFPowerSeriesOnBall F (cauchyPowerSeries F 0 R) 0 R :=
    hFd.hasFPowerSeriesOnBall hRpos
  -- the power series of `A` on the unit disc
  have hArad : (1 : ℝ≥0∞) ≤ (pA a).radius := by
    have := (pA a).le_radius_of_bound 1 (r := 1) (fun n => by
      rw [norm_pA a ha0, NNReal.coe_one, one_pow, mul_one]; exact a_le_one a ha0 hsum n)
    simpa using this
  have hApos : 0 < (pA a).radius := lt_of_lt_of_le zero_lt_one hArad
  have hAps : HasFPowerSeriesOnBall (Aser a) (pA a) 0 1 := by
    have h := ((pA a).hasFPowerSeriesOnBall hApos).mono zero_lt_one hArad
    have hfun : (pA a).sum = Aser a := funext (pA_sum_eq a)
    rwa [hfun] at h
  -- `F = A` near `0`
  have heq : ∀ᶠ z in 𝓝 (0 : ℂ), F z = Aser a z := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hGz := Gfun_ne_zero_of_norm_lt_one ha0 ha_zero hsum hv0 hv hρ'0.le hρ'1 hconv' hz
    have hkey := Gfun_mul_one_sub_Aser ha0 ha_zero hsum hv0 hv hρ'0.le hρ'1 hconv' hz
    have h2 : (1 - z) / Gfun v vlim z = 1 - Aser a z := by
      rw [div_eq_iff hGz]
      linear_combination -hkey
    simp only [hF]
    rw [h2]
    ring
  have hps_eq : cauchyPowerSeries F 0 R = pA a :=
    hFps.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually hAps.hasFPowerSeriesAt heq
  rw [hps_eq] at hFps
  have hrad : (R : ℝ≥0∞) ≤ (pA a).radius := hFps.r_le
  -- geometric moment
  set κ : ℝ≥0 := ⟨(1 + R) / 2, by positivity⟩ with hκ
  have hκ1 : (1 : ℝ) < κ := by show (1 : ℝ) < (1 + (R : ℝ)) / 2; linarith
  have hκR : κ < R := by
    have : (κ : ℝ) < R := by show (1 + (R : ℝ)) / 2 < R; linarith
    exact_mod_cast this
  have hκrad : (κ : ℝ≥0∞) < (pA a).radius := lt_of_lt_of_le (by exact_mod_cast hκR) hrad
  have hsummable := (pA a).summable_norm_mul_pow hκrad
  refine ⟨κ, hκ1, ?_⟩
  refine hsummable.congr (fun n => ?_)
  rw [norm_pA a ha0]

end conclusion

end KendallScratch

open KendallScratch in
theorem solution
    (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha_zero : a 0 = 0) (hsum : HasSum a 1)
    (v : ℕ → ℝ) (hv0 : v 0 = 1)
    (hv : ∀ n : ℕ, v (n + 1) = ∑ j ∈ Finset.range (n + 1), a (j + 1) * v (n - j))
    (vlim M ρ : ℝ) (hvlim : 0 < vlim) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hconv : ∀ n : ℕ, |v n - vlim| ≤ M * ρ ^ n) :
    ∃ κ : ℝ, 1 < κ ∧ Summable (fun k : ℕ => a k * κ ^ k) :=
  kendall_main a ha0 ha_zero hsum v hv0 hv vlim M ρ hvlim hρ0 hρ1 hconv
