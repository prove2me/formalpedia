-- Prove2me | solution 1 for MarkovChainCLT.geoDriftCondition_of_geometricallyErgodic
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T03:31:08.196289+00:00
-- url     : https://prove2.me/submissions/9fb60713-47e8-42f6-8122-9f0b45594392

import Definitions.Def_MarkovDriftMinorization
import Definitions.Def_MarkovErgodicity
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Theorems.Thm_MarkovChainCLT_exists_isSmallSet_measure_pos
import Theorems.Thm_MarkovChainCLT_kendall_summable_geometric_of_renewal_tendsto_geometric
import Theorems.Thm_MarkovChainCLT_measurable_tvDist_kernel

set_option maxHeartbeats 2000000

section
open Filter Finset
open scoped Topology BigOperators

namespace RenewalSeq

/-- geometric partial sums are bounded by `1/(1-x)`. -/
lemma sum_pow_le_inv_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    ∑ m ∈ range k, x ^ m ≤ 1 / (1 - x) := by
  have := (summable_geometric_of_lt_one hx0 hx1).sum_le_tsum (range k) (fun m _ => pow_nonneg hx0 m)
  rwa [tsum_geometric_of_lt_one hx0 hx1, ← one_div] at this

/-- the discrete Grönwall / renewal bootstrap. -/
theorem bootstrap (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (c s θ ρ : ℝ) (hc : 0 ≤ c)
    (hs0 : 0 ≤ s) (hθ : 0 ≤ θ) (hρ0 : 0 ≤ ρ)
    (hrec : ∀ k, T k ≤ c * s ^ k + θ * ∑ i ∈ range k, ρ ^ (k - 1 - i) * T i)
    (r : ℝ) (hr1 : 1 < r) (hrs : r * s ≤ 1) (hrρ : r * ρ < 1) (hrθ : r * (θ + ρ) < 1) :
    ∀ k, T k ≤ (c / (1 - θ * r / (1 - ρ * r))) * r⁻¹ ^ k := by
  have hr0 : 0 < r := by linarith
  have hρr : 0 < 1 - ρ * r := by linarith [mul_comm r ρ]
  set D := 1 - θ * r / (1 - ρ * r) with hDdef
  have hD : 0 < D := by
    rw [hDdef, sub_pos, div_lt_one hρr]
    nlinarith
  set C := c / D with hC
  have hC0 : 0 ≤ C := div_nonneg hc hD.le
  have hCeq : c + C * (1 - D) = C := by
    rw [hC]; field_simp; ring
  have hθD : θ * r / (1 - ρ * r) = 1 - D := by rw [hDdef]; ring
  have hsr : s ≤ r⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hr0, mul_comm]
    exact hrs
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hgeom : ∑ i ∈ range k, ρ ^ (k - 1 - i) * T i ≤ C * (r * r⁻¹ ^ k) / (1 - ρ * r) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [range_zero, sum_empty, pow_zero, mul_one]
        positivity
      · calc ∑ i ∈ range k, ρ ^ (k - 1 - i) * T i
            ≤ ∑ i ∈ range k, ρ ^ (k - 1 - i) * (C * r⁻¹ ^ i) := by
              refine sum_le_sum (fun i hi => ?_)
              exact mul_le_mul_of_nonneg_left (ih i (mem_range.1 hi)) (pow_nonneg hρ0 _)
          _ = C * r⁻¹ ^ (k - 1) * ∑ i ∈ range k, (ρ * r) ^ (k - 1 - i) := by
              rw [mul_sum]
              refine sum_congr rfl (fun i hi => ?_)
              have hi' := mem_range.1 hi
              have hsplit : r⁻¹ ^ (k - 1) = r⁻¹ ^ i * r⁻¹ ^ (k - 1 - i) := by
                rw [← pow_add]; congr 1; omega
              rw [hsplit, mul_pow]
              have hcancel : r⁻¹ ^ (k - 1 - i) * r ^ (k - 1 - i) = 1 := by
                rw [← mul_pow, inv_mul_cancel₀ hr0.ne', one_pow]
              linear_combination (-(C * r⁻¹ ^ i * ρ ^ (k - 1 - i))) * hcancel
          _ ≤ C * r⁻¹ ^ (k - 1) * (1 / (1 - ρ * r)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have := sum_pow_le_inv_one_sub (mul_nonneg hρ0 hr0.le) (by rwa [mul_comm] : ρ * r < 1) k
              rw [show (∑ i ∈ range k, (ρ * r) ^ (k - 1 - i)) = ∑ m ∈ range k, (ρ * r) ^ m from
                sum_range_reflect (fun m => (ρ * r) ^ m) k]
              exact this
          _ = C * (r * r⁻¹ ^ k) / (1 - ρ * r) := by
              have : r⁻¹ ^ (k - 1) = r * r⁻¹ ^ k := by
                obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
                rw [Nat.add_sub_cancel, pow_succ]
                field_simp
              rw [this]; ring
    calc T k ≤ c * s ^ k + θ * ∑ i ∈ range k, ρ ^ (k - 1 - i) * T i := hrec k
      _ ≤ c * r⁻¹ ^ k + θ * (C * (r * r⁻¹ ^ k) / (1 - ρ * r)) := by
          gcongr
      _ = (c + C * (θ * r / (1 - ρ * r))) * r⁻¹ ^ k := by ring
      _ = C * r⁻¹ ^ k := by rw [hθD, hCeq]

/-- **Tannery-type limit for a convolution**: if `c ≥ 0` is summable and `W → L` geometrically,
then `∑_{i<k} c (k-1-i) W i → L ∑ c`. -/
theorem tendsto_conv_of_tendsto (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc : Summable c)
    (W : ℕ → ℝ) (L M ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hW : ∀ i, |W i - L| ≤ M * ρ ^ i) :
    Tendsto (fun k => ∑ i ∈ range k, c (k - 1 - i) * W i) atTop (𝓝 (L * ∑' m, c m)) := by
  have hM : 0 ≤ M := by
    have := hW 0; simp only [pow_zero, mul_one] at this; exact (abs_nonneg _).trans this
  -- `W → L`
  have hWlim : Tendsto W atTop (𝓝 L) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hpow : Tendsto (fun n : ℕ => M * ρ ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul M
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    rw [Real.dist_eq]
    exact (hW n).trans_lt this
  -- reflect the sum
  have hrefl : ∀ k, ∑ i ∈ range k, c (k - 1 - i) * W i = ∑ m ∈ range k, c m * W (k - 1 - m) := by
    intro k
    have := sum_range_reflect (fun i => c (k - 1 - i) * W i) k
    rw [← this]
    refine sum_congr rfl (fun m hm => ?_)
    have hm' := mem_range.1 hm
    congr 2
    omega
  simp_rw [hrefl]
  -- Tannery
  set f : ℕ → ℕ → ℝ := fun k m => if m < k then c m * W (k - 1 - m) else 0 with hf
  have hfsum : ∀ k, ∑ m ∈ range k, c m * W (k - 1 - m) = ∑' m, f k m := by
    intro k
    rw [tsum_eq_sum (s := range k)]
    · refine sum_congr rfl (fun m hm => ?_)
      simp [hf, mem_range.1 hm]
    · intro m hm
      simp [hf, mem_range.not.1 hm]
  simp_rw [hfsum]
  have hLsum : L * ∑' m, c m = ∑' m, c m * L := by rw [tsum_mul_right, mul_comm]
  rw [hLsum]
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => c m * (|L| + M)) ?_ ?_ ?_
  · exact hc.mul_right _
  · intro m
    have h1 : Tendsto (fun k : ℕ => c m * W (k - 1 - m)) atTop (𝓝 (c m * L)) := by
      refine (hWlim.comp ?_).const_mul _
      exact (tendsto_sub_atTop_nat 1).comp (tendsto_sub_atTop_nat m) |> fun h => by
        simpa [Function.comp, Nat.sub_sub] using (tendsto_sub_atTop_nat (1 + m))
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop m] with k hk
    simp [hf, hk]
  · filter_upwards with k
    intro m
    simp only [hf]
    split_ifs with hm
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc0 m)]
      refine mul_le_mul_of_nonneg_left ?_ (hc0 m)
      calc |W (k - 1 - m)| ≤ |L| + |W (k - 1 - m) - L| := by
            have := abs_sub_abs_le_abs_sub (W (k - 1 - m)) L; linarith
        _ ≤ |L| + M := by
            have := hW (k - 1 - m)
            have : M * ρ ^ (k - 1 - m) ≤ M := mul_le_of_le_one_right hM (pow_le_one₀ hρ0 hρ1.le)
            linarith
    · simp only [norm_zero]
      exact mul_nonneg (hc0 m) (by positivity)

/-- `k ≤ r^k / (r - 1)` for `r > 1` (Bernoulli). -/
lemma nat_le_pow_div (r : ℝ) (hr : 1 < r) (k : ℕ) : (k : ℝ) ≤ r ^ k / (r - 1) := by
  have h := one_add_mul_le_pow (a := r - 1) (by linarith) k
  rw [le_div_iff₀ (by linarith)]
  have : 1 + (r - 1) = r := by ring
  rw [this] at h
  nlinarith

/-- **Geometric tails from a renewal-type identity.** If `A ≥ 0` sums to `1` with geometric
decay and `W → L ≥ 0` geometrically, then `B k := W k - ∑_{i<k} A (k-1-i) W i` decays
geometrically, with a rate independent of the constant `M` of `W`. -/
theorem geom_tail_of_conv_identity (A : ℕ → ℝ) (hA0 : ∀ m, 0 ≤ A m) (Ab s : ℝ) (hAb : 0 ≤ Ab)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hA : ∀ m, A m ≤ Ab * s ^ m) (hAsum : HasSum A 1)
    (L : ℝ) (hL : 0 ≤ L) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ r C : ℝ, 1 < r ∧ 0 ≤ C ∧ ∀ (W : ℕ → ℝ) (M : ℝ), 0 ≤ M → (∀ i, |W i - L| ≤ M * ρ ^ i) →
      ∀ k, |W k - ∑ i ∈ range k, A (k - 1 - i) * W i| ≤ C * (1 + M) * r⁻¹ ^ k := by
  set q := max (max s ρ) (1 / 2) with hq
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq1 : q < 1 := max_lt (max_lt hs1 hρ1) (by norm_num)
  have hsq : s ≤ q := (le_max_left _ _).trans (le_max_left _ _)
  have hρq : ρ ≤ q := (le_max_right _ _).trans (le_max_left _ _)
  set r := (Real.sqrt q)⁻¹ with hr
  have hsqrt0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hsqrt1 : Real.sqrt q < 1 := by
    rw [Real.sqrt_lt' (by norm_num)]; simpa using hq1
  have hr1 : 1 < r := by rw [hr]; exact one_lt_inv_iff₀.2 ⟨hsqrt0, hsqrt1⟩
  have hrinv : r⁻¹ = Real.sqrt q := by rw [hr, inv_inv]
  have hqr : q = r⁻¹ ^ 2 := by rw [hrinv, Real.sq_sqrt hq0.le]
  set δ := r - 1 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine ⟨r, 1 + Ab / (δ * q) + L * Ab / (1 - s), hr1, by positivity, ?_⟩
  intro W M hM hW k
  have hr0 : 0 < r := by linarith
  have hrinv0 : 0 ≤ r⁻¹ := by positivity
  have hrinv1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1.le
  -- the three pieces
  have hsplit : W k - ∑ i ∈ range k, A (k - 1 - i) * W i
      = (W k - L) - ∑ i ∈ range k, A (k - 1 - i) * (W i - L) + L * (1 - ∑ m ∈ range k, A m) := by
    have hrefl : ∑ i ∈ range k, A (k - 1 - i) = ∑ m ∈ range k, A m :=
      sum_range_reflect (fun i => A i) k
    have h1 : ∑ i ∈ range k, A (k - 1 - i) * (W i - L)
        = ∑ i ∈ range k, A (k - 1 - i) * W i - L * ∑ m ∈ range k, A m := by
      rw [← hrefl, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl (fun i _ => ?_); ring
    rw [h1]; ring
  -- tail of `A`
  have htail : 1 - ∑ m ∈ range k, A m ≤ Ab / (1 - s) * s ^ k := by
    have h1 := hAsum.summable.sum_add_tsum_nat_add k
    rw [hAsum.tsum_eq] at h1
    have h2 : ∑' m, A (m + k) ≤ ∑' m, Ab * s ^ k * s ^ m := by
      refine Summable.tsum_le_tsum (fun m => ?_) ((summable_nat_add_iff k).2 hAsum.summable)
        ((summable_geometric_of_lt_one hs0 hs1).mul_left _)
      calc A (m + k) ≤ Ab * s ^ (m + k) := hA _
        _ = Ab * s ^ k * s ^ m := by rw [pow_add]; ring
    rw [tsum_mul_left, tsum_geometric_of_lt_one hs0 hs1] at h2
    have : 1 - ∑ m ∈ range k, A m = ∑' m, A (m + k) := by linarith
    rw [this]
    calc ∑' m, A (m + k) ≤ Ab * s ^ k * (1 - s)⁻¹ := h2
      _ = Ab / (1 - s) * s ^ k := by ring
  have htail0 : 0 ≤ 1 - ∑ m ∈ range k, A m := by
    have h1 := hAsum.summable.sum_add_tsum_nat_add k
    rw [hAsum.tsum_eq] at h1
    have : 0 ≤ ∑' m, A (m + k) := tsum_nonneg (fun m => hA0 _)
    linarith
  -- the convolution piece
  have hconv : |∑ i ∈ range k, A (k - 1 - i) * (W i - L)| ≤ Ab * M * (k * q ^ (k - 1)) := by
    calc |∑ i ∈ range k, A (k - 1 - i) * (W i - L)|
        ≤ ∑ i ∈ range k, |A (k - 1 - i) * (W i - L)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range k, Ab * M * q ^ (k - 1) := by
          refine sum_le_sum (fun i hi => ?_)
          have hi' := mem_range.1 hi
          rw [abs_mul, abs_of_nonneg (hA0 _)]
          calc A (k - 1 - i) * |W i - L| ≤ (Ab * s ^ (k - 1 - i)) * (M * ρ ^ i) :=
                mul_le_mul (hA _) (hW i) (abs_nonneg _) (by positivity)
            _ ≤ (Ab * q ^ (k - 1 - i)) * (M * q ^ i) := by
                gcongr
            _ = Ab * M * q ^ (k - 1) := by
                rw [show q ^ (k - 1) = q ^ (k - 1 - i) * q ^ i by rw [← pow_add]; congr 1; omega]
                ring
      _ = Ab * M * (k * q ^ (k - 1)) := by
          rw [sum_const, card_range, nsmul_eq_mul]; ring
  -- `k q^(k-1) ≤ r⁻¹^k / (δ q)`
  have hkq : (k : ℝ) * q ^ (k - 1) ≤ r⁻¹ ^ k / (δ * q) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp; positivity
    · have h1 : (k : ℝ) * q ^ (k - 1) = (k : ℝ) * q ^ k / q := by
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]; field_simp
      rw [h1, ← div_div]
      refine div_le_div_of_nonneg_right ?_ hq0.le
      have h2 := nat_le_pow_div r hr1 k
      calc (k : ℝ) * q ^ k ≤ r ^ k / (r - 1) * q ^ k :=
            mul_le_mul_of_nonneg_right h2 (pow_nonneg hq0.le k)
        _ = (r * q) ^ k / δ := by rw [mul_pow, hδ]; ring
        _ = r⁻¹ ^ k / δ := by
            congr 2
            rw [hqr, pow_two, ← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul]
  -- assemble
  rw [hsplit]
  have hq_le : q ^ k ≤ r⁻¹ ^ k := by
    rw [hqr, ← pow_mul]
    exact pow_le_pow_of_le_one hrinv0 hrinv1 (by omega)
  have hs_le : s ^ k ≤ r⁻¹ ^ k := (pow_le_pow_left₀ hs0 hsq k).trans hq_le
  have hρ_le : ρ ^ k ≤ r⁻¹ ^ k := (pow_le_pow_left₀ hρ0 hρq k).trans hq_le
  calc |W k - L - ∑ i ∈ range k, A (k - 1 - i) * (W i - L) + L * (1 - ∑ m ∈ range k, A m)|
      ≤ |W k - L| + |∑ i ∈ range k, A (k - 1 - i) * (W i - L)| + |L * (1 - ∑ m ∈ range k, A m)| := by
        have := abs_add_three (W k - L) (-(∑ i ∈ range k, A (k - 1 - i) * (W i - L)))
          (L * (1 - ∑ m ∈ range k, A m))
        rw [abs_neg] at this
        simpa [sub_eq_add_neg] using this
    _ ≤ M * r⁻¹ ^ k + Ab * M * (r⁻¹ ^ k / (δ * q)) + L * (Ab / (1 - s) * r⁻¹ ^ k) := by
        gcongr
        · exact (hW k).trans (mul_le_mul_of_nonneg_left hρ_le hM)
        · exact hconv.trans (mul_le_mul_of_nonneg_left hkq (by positivity))
        · rw [abs_mul, abs_of_nonneg hL, abs_of_nonneg htail0]
          exact mul_le_mul_of_nonneg_left (htail.trans (mul_le_mul_of_nonneg_left hs_le
            (by positivity))) hL
    _ = (M + Ab * M / (δ * q) + L * Ab / (1 - s)) * r⁻¹ ^ k := by ring
    _ ≤ (1 + Ab / (δ * q) + L * Ab / (1 - s)) * (1 + M) * r⁻¹ ^ k := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h1 : 0 ≤ Ab / (δ * q) := by positivity
        have h2 : 0 ≤ L * Ab / (1 - s) := by
          have : 0 < 1 - s := by linarith
          positivity
        have e1 : Ab * M / (δ * q) = Ab / (δ * q) * M := by ring
        rw [e1]
        nlinarith [mul_nonneg h1 hM, mul_nonneg h2 hM]


end RenewalSeq
end

section
open Filter Finset
open scoped Topology BigOperators

namespace RenewalSeq

/-- the tail-sum identity for a nonneg telescoping sequence tending to `0`. -/
lemma hasSum_tail_of_telescoping (rr B : ℕ → ℝ) (hB0 : ∀ m, 0 ≤ B m)
    (hrec : ∀ m, rr m = rr (m + 1) + B m) (hlim : Tendsto rr atTop (𝓝 0)) (k : ℕ) :
    HasSum (fun m => B (m + k)) (rr k) := by
  have hpartial : ∀ n, ∑ m ∈ range n, B (m + k) = rr k - rr (n + k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, hrec (n + k)]
      rw [show n + 1 + k = n + k + 1 by ring]; ring
  have hnn : ∀ m, 0 ≤ B (m + k) := fun m => hB0 _
  refine (hasSum_iff_tendsto_nat_of_nonneg hnn _).2 ?_
  simp_rw [hpartial]
  have : Tendsto (fun n => rr (n + k)) atTop (𝓝 0) :=
    hlim.comp (tendsto_add_atTop_nat k)
  simpa using tendsto_const_nhds.sub this

/-- geometric convergence gives convergence. -/
lemma tendsto_of_geom_bound (u : ℕ → ℝ) (L M ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ k, |u k - L| ≤ M * ρ ^ k) : Tendsto u atTop (𝓝 L) := by
  have hM : 0 ≤ M := by
    have := h 0; simp only [pow_zero, mul_one] at this; exact (abs_nonneg _).trans this
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hpow : Tendsto (fun n : ℕ => M * ρ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul M
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
  rw [Real.dist_eq]; exact (h n).trans_lt this

/-- **Kendall's theorem in the `A/u` normalisation**: `u k = A k + ∑_{j<k} A (k-1-j) u j`. -/
theorem kendall_A_form (A u : ℕ → ℝ) (hA0 : ∀ m, 0 ≤ A m) (hAsum : HasSum A 1)
    (hu : ∀ k, u k = A k + ∑ j ∈ range k, A (k - 1 - j) * u j)
    (L MQ ρ : ℝ) (hL : 0 < L) (hMQ : 0 ≤ MQ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (huconv : ∀ k, |u k - L| ≤ MQ * ρ ^ k) :
    ∃ κ : ℝ, 1 < κ ∧ Summable (fun m => A m * κ ^ m) := by
  set a : ℕ → ℝ := fun j => if j = 0 then 0 else A (j - 1) with ha
  set v : ℕ → ℝ := fun n => if n = 0 then 1 else u (n - 1) with hv
  set ρ' := max ρ (1 / 2) with hρ'
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hρ'1 : ρ' < 1 := max_lt hρ1 (by norm_num)
  have hρρ' : ρ ≤ ρ' := le_max_left _ _
  have ha0 : ∀ j, 0 ≤ a j := fun j => by
    simp only [ha]; split_ifs <;> simp [hA0]
  have hsum : HasSum a 1 := by
    have h2 : HasSum (fun n => a (n + 1)) (1 - ∑ i ∈ range 1, a i) := by
      have h1 : ∑ i ∈ range 1, a i = 0 := by simp [ha]
      rw [h1, sub_zero]
      simpa [ha] using hAsum
    exact (hasSum_nat_add_iff' 1).mp h2
  have hvrec : ∀ n : ℕ, v (n + 1) = ∑ j ∈ range (n + 1), a (j + 1) * v (n - j) := by
    intro n
    simp only [hv, ha, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [sum_range_succ, Nat.sub_self]
    simp only [if_true, mul_one]
    have hrefl : ∑ j ∈ range n, A j * (if n - j = 0 then (1 : ℝ) else u (n - j - 1))
        = ∑ j ∈ range n, A (n - 1 - j) * u j := by
      rw [← sum_range_reflect (fun j => A (n - 1 - j) * u j) n]
      refine sum_congr rfl (fun j hj => ?_)
      have hj' := mem_range.1 hj
      have h1 : n - j ≠ 0 := by omega
      have h2 : n - j - 1 = n - 1 - j := by omega
      have h3 : n - 1 - (n - 1 - j) = j := by omega
      rw [if_neg h1, h2, h3]
    rw [hrefl, hu n]
    ring
  have hconv : ∀ n : ℕ, |v n - L| ≤ max (MQ / ρ') |1 - L| * ρ' ^ n := by
    intro n
    rcases n with _ | n
    · simp only [hv, if_true, pow_zero, mul_one]
      exact le_max_right _ _
    · simp only [hv, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      calc |u n - L| ≤ MQ * ρ ^ n := huconv n
        _ ≤ MQ * ρ' ^ n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρρ' n) hMQ
        _ = MQ / ρ' * ρ' ^ (n + 1) := by rw [pow_succ]; field_simp
        _ ≤ max (MQ / ρ') |1 - L| * ρ' ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  obtain ⟨κ, hκ1, hκ⟩ := MarkovChainCLT.kendall_summable_geometric_of_renewal_tendsto_geometric a ha0 (by simp [ha]) hsum v (by simp [hv]) hvrec
    L _ ρ' hL hρ'0.le hρ'1 hconv
  refine ⟨κ, hκ1, ?_⟩
  have h1 : Summable (fun m => a (m + 1) * κ ^ (m + 1)) := (summable_nat_add_iff 1).2 hκ
  have h2 : (fun m => a (m + 1) * κ ^ (m + 1)) = fun m => κ * (A m * κ ^ m) := by
    funext m; simp only [ha, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]; ring
  rw [h2] at h1
  have hκ0 : κ ≠ 0 := by positivity
  simpa [hκ0] using h1.mul_left κ⁻¹

/-- **the renewal package.** -/
theorem renewal_package (A u q : ℕ → ℝ) (L MQ ρ : ℝ) (hL : 0 < L) (hMQ : 0 ≤ MQ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hA0 : ∀ m, 0 ≤ A m)
    (hu : ∀ k, u k = A k + ∑ j ∈ range k, A (k - 1 - j) * u j)
    (huconv : ∀ k, |u k - L| ≤ MQ * ρ ^ k)
    (hq0 : q 0 = 1) (hqnn : ∀ m, 0 ≤ q m) (hq : ∀ m, q m = q (m + 1) + A m)
    (hqtot : ∀ k, (1 : ℝ) = q k + ∑ j ∈ range k, u j * q (k - 1 - j)) :
    ∃ r C₀ : ℝ, 1 < r ∧ 0 ≤ C₀ ∧
      ∀ (W B rr : ℕ → ℝ) (M : ℝ), 0 ≤ M → (∀ k, |W k - L| ≤ M * ρ ^ k) →
        (∀ k, W k = B k + ∑ j ∈ range k, A (k - 1 - j) * W j) →
        (∀ m, 0 ≤ B m) → (∀ m, 0 ≤ rr m) → (∀ m, rr m = rr (m + 1) + B m) →
        (∀ k, (1 : ℝ) = rr k + ∑ j ∈ range k, W j * q (k - 1 - j)) →
        ∀ k, rr k ≤ C₀ * (1 + M) * r⁻¹ ^ k := by
  -- partial sums of `A`
  have hApartial : ∀ k, ∑ m ∈ range k, A m = 1 - q k := by
    intro k
    induction k with
    | zero => simp [hq0]
    | succ k ih => rw [sum_range_succ, ih, hq k]; ring
  have hAsummable : Summable A := by
    refine summable_of_sum_range_le hA0 (c := 1) (fun k => ?_)
    rw [hApartial]; linarith [hqnn k]
  have hulim : Tendsto u atTop (𝓝 L) := tendsto_of_geom_bound u L MQ ρ hρ0 hρ1 huconv
  -- `∑ A = 1` via Tannery
  have hAsum : HasSum A 1 := by
    have hconv := tendsto_conv_of_tendsto A hA0 hAsummable u L MQ ρ hρ0 hρ1 huconv
    have hA0lim : Tendsto A atTop (𝓝 0) := hAsummable.tendsto_atTop_zero
    have hulim2 : Tendsto u atTop (𝓝 (0 + L * ∑' m, A m)) :=
      (hA0lim.add hconv).congr (fun k => (hu k).symm)
    have heq : L = 0 + L * ∑' m, A m := tendsto_nhds_unique hulim hulim2
    have : ∑' m, A m = 1 := by
      have h := mul_left_cancel₀ hL.ne' (show L * ∑' m, A m = L * 1 by linarith)
      exact h
    exact hAsummable.hasSum_iff.2 this
  -- `q → 0`
  have hqlim : Tendsto q atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ∑ m ∈ range k, A m) atTop (𝓝 1) := hAsum.tendsto_sum_nat
    have h2 : Tendsto (fun k => 1 - ∑ m ∈ range k, A m) atTop (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub h1
    simp only [sub_self] at h2
    refine h2.congr (fun k => ?_)
    rw [hApartial]; ring
  -- Kendall: geometric tail of `A`
  obtain ⟨κ, hκ1, hκsum⟩ := kendall_A_form A u hA0 hAsum hu L MQ ρ hL hMQ hρ0 hρ1 huconv
  set Ab := ∑' m, A m * κ ^ m with hAb
  have hAb0 : 0 ≤ Ab := tsum_nonneg (fun m => mul_nonneg (hA0 m) (by positivity))
  have hκ0 : 0 < κ := by linarith
  have hκinv0 : 0 ≤ κ⁻¹ := by positivity
  have hκinv1 : κ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hκ1
  have hAgeom : ∀ m, A m ≤ Ab * κ⁻¹ ^ m := by
    intro m
    have h := hκsum.le_tsum m (fun j _ => mul_nonneg (hA0 j) (by positivity))
    rw [← hAb] at h
    have hk : (0:ℝ) < κ ^ m := by positivity
    calc A m = A m * κ ^ m * κ⁻¹ ^ m := by
          rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hκ0.ne', one_pow, mul_one]
      _ ≤ Ab * κ⁻¹ ^ m := mul_le_mul_of_nonneg_right h (by positivity)
  obtain ⟨r, C₀', hr1, hC₀', hB⟩ := geom_tail_of_conv_identity A hA0 Ab κ⁻¹ hAb0 hκinv0 hκinv1
    hAgeom hAsum L hL.le ρ hρ0 hρ1
  -- `q` is summable
  have hqtail : ∀ k, q k = ∑' m, A (m + k) := by
    intro k
    have h := hAsum.summable.sum_add_tsum_nat_add k
    rw [hAsum.tsum_eq, hApartial] at h
    linarith
  have hqle : ∀ k, q k ≤ Ab / (1 - κ⁻¹) * κ⁻¹ ^ k := by
    intro k
    rw [hqtail]
    have h2 : ∑' m, A (m + k) ≤ ∑' m, Ab * κ⁻¹ ^ k * κ⁻¹ ^ m := by
      refine Summable.tsum_le_tsum (fun m => ?_) ((summable_nat_add_iff k).2 hAsum.summable)
        ((summable_geometric_of_lt_one hκinv0 hκinv1).mul_left _)
      calc A (m + k) ≤ Ab * κ⁻¹ ^ (m + k) := hAgeom _
        _ = Ab * κ⁻¹ ^ k * κ⁻¹ ^ m := by rw [pow_add]; ring
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hκinv0])] at h2
    calc ∑' m, A (m + k) ≤ Ab * κ⁻¹ ^ k * (1 - κ⁻¹)⁻¹ := h2
      _ = Ab / (1 - κ⁻¹) * κ⁻¹ ^ k := by ring
  have hqsummable : Summable q :=
    Summable.of_nonneg_of_le hqnn hqle ((summable_geometric_of_lt_one hκinv0 hκinv1).mul_left _)
  -- the common limit `1 - L ∑ q` is `0`
  have hlimit : ∀ (W rr : ℕ → ℝ) (M : ℝ), (∀ k, |W k - L| ≤ M * ρ ^ k) →
      (∀ k, (1 : ℝ) = rr k + ∑ j ∈ range k, W j * q (k - 1 - j)) →
      Tendsto rr atTop (𝓝 (1 - L * ∑' m, q m)) := by
    intro W rr M hW hrr
    have hconv := tendsto_conv_of_tendsto q hqnn hqsummable W L M ρ hρ0 hρ1 hW
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hconv
    refine h.congr (fun k => ?_)
    have := hrr k
    have hcomm : ∑ i ∈ range k, q (k - 1 - i) * W i = ∑ j ∈ range k, W j * q (k - 1 - j) :=
      sum_congr rfl (fun j _ => mul_comm _ _)
    rw [hcomm]; linarith
  have hzero : 1 - L * ∑' m, q m = 0 := by
    have h1 := hlimit u q MQ huconv hqtot
    exact (tendsto_nhds_unique h1 hqlim)
  -- conclusion
  have hr0 : 0 < r := by linarith
  have hrinv0 : 0 ≤ r⁻¹ := by positivity
  have hrinv1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  refine ⟨r, C₀' / (1 - r⁻¹), hr1, by
    have : 0 < 1 - r⁻¹ := by linarith
    positivity, ?_⟩
  intro W B rr M hM hW hWB hB0 hrr0 hrrrec hrrtot k
  have hrrlim : Tendsto rr atTop (𝓝 0) := by
    have := hlimit W rr M hW hrrtot
    rwa [hzero] at this
  have hrrsum := hasSum_tail_of_telescoping rr B hB0 hrrrec hrrlim k
  have hBle : ∀ m, B m ≤ C₀' * (1 + M) * r⁻¹ ^ m := by
    intro m
    have h := hB W M hM hW m
    have hBm : B m = W m - ∑ i ∈ range m, A (m - 1 - i) * W i := by linarith [hWB m]
    rw [hBm]
    exact (le_abs_self _).trans h
  have hgeomsum : HasSum (fun m => C₀' * (1 + M) * r⁻¹ ^ k * r⁻¹ ^ m)
      (C₀' * (1 + M) * r⁻¹ ^ k * (1 - r⁻¹)⁻¹) :=
    (hasSum_geometric_of_lt_one hrinv0 hrinv1).mul_left _
  calc rr k ≤ C₀' * (1 + M) * r⁻¹ ^ k * (1 - r⁻¹)⁻¹ := by
        refine hasSum_le (fun m => ?_) hrrsum hgeomsum
        calc B (m + k) ≤ C₀' * (1 + M) * r⁻¹ ^ (m + k) := hBle _
          _ = C₀' * (1 + M) * r⁻¹ ^ k * r⁻¹ ^ m := by rw [pow_add]; ring
    _ = C₀' / (1 - r⁻¹) * (1 + M) * r⁻¹ ^ k := by ring

end RenewalSeq
end

section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

namespace Regen

variable {X : Type*} [MeasurableSpace X]

/-- `iterKernel P (m + n) = iterKernel P m ∘ₖ iterKernel P n`. -/
lemma iterKernel_add (P : Kernel X X) (m n : ℕ) :
    iterKernel P (m + n) = iterKernel P m ∘ₖ iterKernel P n := by
  induction m with
  | zero => simp [iterKernel_zero, Kernel.id_comp]
  | succ m ih =>
    rw [Nat.succ_add, iterKernel_succ, ih, iterKernel_succ, Kernel.comp_assoc]

lemma id_comp_measure (μ : Measure X) : (Kernel.id : Kernel X X) ∘ₘ μ = μ := by
  show μ.bind (Kernel.id : Kernel X X) = μ
  have : (⇑(Kernel.id : Kernel X X)) = Measure.dirac := funext (fun x => Kernel.id_apply x)
  rw [this, Measure.bind_dirac]

lemma comp_sum_range (κ : Kernel X X) (f : ℕ → Measure X) (k : ℕ) :
    κ ∘ₘ (∑ j ∈ range k, f j) = ∑ j ∈ range k, κ ∘ₘ f j := by
  induction k with
  | zero => simp [Measure.bind_zero_left]
  | succ k ih => rw [sum_range_succ, Measure.comp_add, ih, sum_range_succ]

/-- the regeneration kernel `E(x, ·) = ε 1_C(x) Q`. -/
noncomputable def Ereg (C : Set X) (hC : MeasurableSet C) (ε : ℝ) (Q : Measure X) : Kernel X X :=
  Kernel.mk (fun x => C.indicator (fun _ => ENNReal.ofReal ε) x • Q) (by
    refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
    simp only [Measure.smul_apply, smul_eq_mul]
    exact (measurable_const.indicator hC).mul_const _)

lemma Ereg_apply (C : Set X) (hC : MeasurableSet C) (ε : ℝ) (Q : Measure X) (x : X) :
    Ereg C hC ε Q x = C.indicator (fun _ => ENNReal.ofReal ε) x • Q := rfl

lemma Ereg_apply_set (C : Set X) (hC : MeasurableSet C) (ε : ℝ) (Q : Measure X) (x : X)
    (A : Set X) : Ereg C hC ε Q x A = C.indicator (fun _ => ENNReal.ofReal ε * Q A) x := by
  rw [Ereg_apply, Measure.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ C <;> simp [hx]

instance Ereg.instIsFiniteMeasure (C : Set X) (hC : MeasurableSet C) (ε : ℝ) (Q : Measure X)
    [IsFiniteMeasure Q] (x : X) : IsFiniteMeasure (Ereg C hC ε Q x) := by
  constructor
  rw [Ereg_apply, Measure.smul_apply, smul_eq_mul]
  refine ENNReal.mul_lt_top ?_ (measure_lt_top _ _)
  exact lt_of_le_of_lt (Set.indicator_le (fun _ _ => le_rfl) x) ENNReal.ofReal_lt_top

/-- `E ∘ₘ μ = (μ C · ε) • Q`. -/
lemma Ereg_comp (C : Set X) (hC : MeasurableSet C) (ε : ℝ) (Q : Measure X) (μ : Measure X) :
    Ereg C hC ε Q ∘ₘ μ = (μ C * ENNReal.ofReal ε) • Q := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _), Measure.smul_apply, smul_eq_mul]
  simp_rw [Ereg_apply_set]
  rw [lintegral_indicator_const hC]
  ring

section residual

variable (P : Kernel X X) [IsMarkovKernel P] (n₀ : ℕ) (C : Set X) (hC : MeasurableSet C)
  (ε : ℝ) (Q : Measure X) [IsProbabilityMeasure Q]
  (hmin : ∀ x ∈ C, ∀ A, MeasurableSet A → ENNReal.ofReal ε * Q A ≤ (iterKernel P n₀) x A)

include hmin in
lemma Ereg_le (x : X) : Ereg C hC ε Q x ≤ iterKernel P n₀ x := by
  rw [Ereg_apply]
  by_cases hx : x ∈ C
  · simp only [hx, Set.indicator_of_mem]
    refine Measure.le_iff.2 (fun A hA => ?_)
    rw [Measure.smul_apply, smul_eq_mul]
    exact hmin x hx A hA
  · simp only [hx, Set.indicator_of_notMem, not_false_eq_true, zero_smul]
    exact Measure.zero_le _

include hmin in
/-- the residual (sub-Markov) kernel `R = P^{n₀} − E`. -/
noncomputable def Rres : Kernel X X :=
  Kernel.mk (fun x => iterKernel P n₀ x - Ereg C hC ε Q x) (by
    refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
    have : (fun x => (iterKernel P n₀ x - Ereg C hC ε Q x) A)
        = fun x => iterKernel P n₀ x A - Ereg C hC ε Q x A := by
      funext x
      exact Measure.sub_apply hA (Ereg_le P n₀ C hC ε Q hmin x)
    rw [this]
    exact (Kernel.measurable_coe _ hA).sub (Kernel.measurable_coe _ hA))

lemma Rres_apply (x : X) :
    Rres P n₀ C hC ε Q hmin x = iterKernel P n₀ x - Ereg C hC ε Q x := rfl

lemma Rres_add_Ereg : Rres P n₀ C hC ε Q hmin + Ereg C hC ε Q = iterKernel P n₀ := by
  ext x : 1
  rw [Kernel.add_apply, Rres_apply]
  exact Measure.sub_add_cancel_of_le (Ereg_le P n₀ C hC ε Q hmin x)

/-- **Regeneration expansion by the last regeneration**, at the level of initial measures. -/
theorem skeleton_expansion (ν : Measure X) (k : ℕ) :
    iterKernel P (n₀ * k) ∘ₘ ν =
      iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ ν +
      ∑ j ∈ range k, (((iterKernel P (n₀ * j)) ∘ₘ ν) C * ENNReal.ofReal ε) •
        (iterKernel (Rres P n₀ C hC ε Q hmin) (k - 1 - j) ∘ₘ Q) := by
  induction k with
  | zero => simp [iterKernel_zero]
  | succ k ih =>
    set R := Rres P n₀ C hC ε Q hmin with hR
    have hstep : iterKernel P (n₀ * (k + 1)) = iterKernel P n₀ ∘ₖ iterKernel P (n₀ * k) := by
      rw [Nat.mul_succ, add_comm, iterKernel_add]
    have hRcomp : R ∘ₘ (iterKernel P (n₀ * k) ∘ₘ ν)
        = iterKernel R (k + 1) ∘ₘ ν +
          ∑ j ∈ range k, (((iterKernel P (n₀ * j)) ∘ₘ ν) C * ENNReal.ofReal ε) •
            (iterKernel R (k + 1 - 1 - j) ∘ₘ Q) := by
      rw [ih, Measure.comp_add, comp_sum_range, iterKernel_succ, Measure.comp_assoc]
      congr 1
      refine sum_congr rfl (fun j hj => ?_)
      have hj' := mem_range.1 hj
      rw [show k + 1 - 1 - j = k - 1 - j + 1 by omega, Measure.comp_smul, Measure.comp_assoc,
        ← iterKernel_succ]
    have hlast : iterKernel R (k + 1 - 1 - k) ∘ₘ Q = Q := by
      rw [show k + 1 - 1 - k = 0 by omega, iterKernel_zero, id_comp_measure]
    rw [hstep, ← Measure.comp_assoc, ← Rres_add_Ereg P n₀ C hC ε Q hmin, Measure.add_comp,
      Ereg_comp, ← hR, hRcomp, sum_range_succ, hlast, add_assoc]

/-! ### Total mass and comparison -/

lemma comp_apply_univ_of_isMarkov (κ : Kernel X X) [IsMarkovKernel κ] (μ : Measure X) :
    (κ ∘ₘ μ) Set.univ = μ Set.univ := by
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
  simp

lemma Rk_comp_le_one (ν : Measure X) [IsProbabilityMeasure ν] (k : ℕ) (A : Set X) :
    (iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ ν) A ≤ 1 := by
  have h := congrArg (fun μ : Measure X => μ A) (skeleton_expansion P n₀ C hC ε Q hmin ν k)
  simp only [Measure.add_apply] at h
  calc (iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ ν) A
      ≤ (iterKernel P (n₀ * k) ∘ₘ ν) A := by rw [h]; exact le_add_right le_rfl
    _ ≤ (iterKernel P (n₀ * k) ∘ₘ ν) Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := by rw [comp_apply_univ_of_isMarkov, measure_univ]

lemma Rk_comp_ne_top (ν : Measure X) [IsProbabilityMeasure ν] (k : ℕ) (A : Set X) :
    (iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ ν) A ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (Rk_comp_le_one P n₀ C hC ε Q hmin ν k A)

/-- one residual step removes exactly the regenerating mass: `(R ∘ₘ μ) univ + ε μ C = μ univ`. -/
lemma Rres_comp_univ (μ : Measure X) :
    (Rres P n₀ C hC ε Q hmin ∘ₘ μ) Set.univ + μ C * ENNReal.ofReal ε = μ Set.univ := by
  have h := congrArg (fun m : Measure X => m Set.univ)
    (congrArg (fun κ : Kernel X X => κ ∘ₘ μ) (Rres_add_Ereg P n₀ C hC ε Q hmin))
  simp only [Measure.add_comp, Measure.add_apply, Ereg_comp, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one] at h
  rw [h, comp_apply_univ_of_isMarkov]

/-! ### The real sequences -/

variable (ν : Measure X) [IsProbabilityMeasure ν]

/-- `W_ν(k) = ε (P^{n₀k} ν)(C)`: regeneration probability at skeleton step `k+1`. -/
noncomputable def Wseq (k : ℕ) : ℝ := ε * ((iterKernel P (n₀ * k) ∘ₘ ν) C).toReal

/-- `B_ν(k) = ε (R^k ν)(C)`: first regeneration at skeleton step `k+1`. -/
noncomputable def Bseq (k : ℕ) : ℝ := ε * ((iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ ν) C).toReal

/-- `r_ν(k) = (R^k ν)(X)`: no regeneration in the first `k` skeleton steps. -/
noncomputable def rseq (k : ℕ) : ℝ := ((iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ ν) Set.univ).toReal

variable (hε : 0 ≤ ε)

include hε in
lemma Wseq_nonneg (k : ℕ) : 0 ≤ Wseq P n₀ C ε ν k := mul_nonneg hε ENNReal.toReal_nonneg

include hε in
lemma Bseq_nonneg (k : ℕ) : 0 ≤ Bseq P n₀ C hC ε Q hmin ν k := mul_nonneg hε ENNReal.toReal_nonneg

lemma rseq_nonneg (k : ℕ) : 0 ≤ rseq P n₀ C hC ε Q hmin ν k := ENNReal.toReal_nonneg

lemma rseq_le_one (k : ℕ) : rseq P n₀ C hC ε Q hmin ν k ≤ 1 := by
  unfold rseq
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (Rk_comp_le_one P n₀ C hC ε Q hmin ν k _)

include hε in
/-- **first-passage identity**: `W_ν(k) = B_ν(k) + ∑_{j<k} A(k-1-j) W_ν(j)`. -/
theorem Wseq_eq (k : ℕ) :
    Wseq P n₀ C ε ν k = Bseq P n₀ C hC ε Q hmin ν k +
      ∑ j ∈ range k, Bseq P n₀ C hC ε Q hmin Q (k - 1 - j) * Wseq P n₀ C ε ν j := by
  have h := congrArg (fun μ : Measure X => μ C) (skeleton_expansion P n₀ C hC ε Q hmin ν k)
  simp only [Measure.add_apply, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul] at h
  unfold Wseq Bseq
  rw [h, ENNReal.toReal_add (Rk_comp_ne_top P n₀ C hC ε Q hmin ν k C)
    (ENNReal.sum_ne_top.2 (fun j _ => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
        ((measure_mono (Set.subset_univ _)).trans (by
          rw [comp_apply_univ_of_isMarkov, measure_univ]))) ENNReal.ofReal_ne_top)
      (Rk_comp_ne_top P n₀ C hC ε Q hmin Q _ C))),
    ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
        ((measure_mono (Set.subset_univ _)).trans (by
          rw [comp_apply_univ_of_isMarkov, measure_univ]))) ENNReal.ofReal_ne_top)
      (Rk_comp_ne_top P n₀ C hC ε Q hmin Q _ C)),
    mul_add, mul_sum]
  congr 1
  refine sum_congr rfl (fun j _ => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε]
  ring

include hε in
/-- **total-mass identity**: `1 = r_ν(k) + ∑_{j<k} W_ν(j) q(k-1-j)` with `q = r_Q`. -/
theorem rseq_eq (k : ℕ) :
    (1 : ℝ) = rseq P n₀ C hC ε Q hmin ν k +
      ∑ j ∈ range k, Wseq P n₀ C ε ν j * rseq P n₀ C hC ε Q hmin Q (k - 1 - j) := by
  have h := congrArg (fun μ : Measure X => μ Set.univ) (skeleton_expansion P n₀ C hC ε Q hmin ν k)
  simp only [Measure.add_apply, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, comp_apply_univ_of_isMarkov, measure_univ] at h
  unfold Wseq rseq
  have hε' : 0 ≤ ε := hε
  rw [← ENNReal.toReal_one, h, ENNReal.toReal_add (Rk_comp_ne_top P n₀ C hC ε Q hmin ν k _)
    (ENNReal.sum_ne_top.2 (fun j _ => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
        ((measure_mono (Set.subset_univ _)).trans (by
          rw [comp_apply_univ_of_isMarkov, measure_univ]))) ENNReal.ofReal_ne_top)
      (Rk_comp_ne_top P n₀ C hC ε Q hmin Q _ _))),
    ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
        ((measure_mono (Set.subset_univ _)).trans (by
          rw [comp_apply_univ_of_isMarkov, measure_univ]))) ENNReal.ofReal_ne_top)
      (Rk_comp_ne_top P n₀ C hC ε Q hmin Q _ _))]
  congr 1
  refine sum_congr rfl (fun j _ => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε']
  ring

include hε in
/-- **telescoping**: `r_ν(m) = r_ν(m+1) + B_ν(m)`. -/
theorem rseq_succ (m : ℕ) :
    rseq P n₀ C hC ε Q hmin ν m = rseq P n₀ C hC ε Q hmin ν (m + 1) + Bseq P n₀ C hC ε Q hmin ν m := by
  unfold rseq Bseq
  have h := Rres_comp_univ P n₀ C hC ε Q hmin (iterKernel (Rres P n₀ C hC ε Q hmin) m ∘ₘ ν)
  rw [Measure.comp_assoc, ← iterKernel_succ] at h
  rw [← h, ENNReal.toReal_add (Rk_comp_ne_top P n₀ C hC ε Q hmin ν _ _)
    (ENNReal.mul_ne_top (Rk_comp_ne_top P n₀ C hC ε Q hmin ν _ _) ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hε]
  ring


end residual

end Regen
end

section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT Regen RenewalSeq

namespace Regen

variable {X : Type*} [MeasurableSpace X]

/-- `|μ(C) - π(C)| ≤ ‖μ - π‖` for probability measures. -/
lemma abs_toReal_sub_le_tvDist (μ π : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    {C : Set X} (hC : MeasurableSet C) :
    |(μ C).toReal - (π C).toReal| ≤ tvDist μ π := by
  unfold tvDist
  refine le_csSup ⟨1, ?_⟩ ⟨C, hC, rfl⟩
  rintro r ⟨A, _, rfl⟩
  have h1 : (μ A).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have h2 : (π A).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (π A).toReal := ENNReal.toReal_nonneg
  rw [abs_sub_le_iff]; constructor <;> linarith

section rates

variable (P : Kernel X X) [IsMarkovKernel P] (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (C : Set X)
  (hC : MeasurableSet C) (ε : ℝ) (hε : 0 ≤ ε) (Q : Measure X) [IsProbabilityMeasure Q]
  (hmin : ∀ x ∈ C, ∀ A, MeasurableSet A → ENNReal.ofReal ε * Q A ≤ (iterKernel P n₀) x A)
  (π : Measure X) [IsProbabilityMeasure π] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)

include hn₀ hC hε ht0 ht1 in
/-- pointwise version: the skeleton started from `P^j(x, ·)`. -/
lemma Wseq_conv_iter (x : X) (j : ℕ) (Mx : ℝ) (hMx : 0 ≤ Mx)
    (hrate : ∀ n, 1 ≤ n → tvDist (iterKernel P n x) π ≤ Mx * t ^ n) (k : ℕ) :
    |Wseq P n₀ C ε (iterKernel P j x) k - ε * (π C).toReal| ≤ ε * (Mx + 1) * (t ^ n₀) ^ k := by
  unfold Wseq
  have hcomp : iterKernel P (n₀ * k) ∘ₘ iterKernel P j x = iterKernel P (n₀ * k + j) x := by
    rw [iterKernel_add, Kernel.comp_apply]
  rw [hcomp, ← mul_sub, abs_mul, abs_of_nonneg hε, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hε
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- lag 0: crude bound by 1
    simp only [pow_zero, mul_one]
    have h1 : ((iterKernel P (n₀ * 0 + j) x) C).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    have h2 : (π C).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    have h3 : 0 ≤ ((iterKernel P (n₀ * 0 + j) x) C).toReal := ENNReal.toReal_nonneg
    have h4 : 0 ≤ (π C).toReal := ENNReal.toReal_nonneg
    rw [abs_sub_le_iff]; constructor <;> linarith
  · calc |((iterKernel P (n₀ * k + j) x) C).toReal - (π C).toReal|
        ≤ tvDist (iterKernel P (n₀ * k + j) x) π := abs_toReal_sub_le_tvDist _ _ hC
      _ ≤ Mx * t ^ (n₀ * k + j) := hrate _ (by nlinarith)
      _ ≤ Mx * (t ^ n₀) ^ k := by
          rw [← pow_mul]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht0 ht1.le (by omega)) hMx
      _ ≤ (Mx + 1) * (t ^ n₀) ^ k := by
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

include hn₀ hC hε ht0 ht1 in
/-- integrated version: the skeleton started from `Q`, whose points have a uniform rate. -/
lemma Wseq_conv_Q (KQ : ℝ) (hKQ : 0 ≤ KQ)
    (hrateQ : ∀ n, 1 ≤ n → ∀ᵐ x ∂Q, tvDist (iterKernel P n x) π ≤ KQ * t ^ n) (k : ℕ) :
    |Wseq P n₀ C ε Q k - ε * (π C).toReal| ≤ ε * (KQ + 1) * (t ^ n₀) ^ k := by
  unfold Wseq
  rw [← mul_sub, abs_mul, abs_of_nonneg hε, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hε
  have hbound1 : ∀ μ : Measure X, IsProbabilityMeasure μ → |(μ C).toReal - (π C).toReal| ≤ 1 := by
    intro μ hμ
    have h1 : (μ C).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    have h2 : (π C).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    have h3 : 0 ≤ (μ C).toReal := ENNReal.toReal_nonneg
    have h4 : 0 ≤ (π C).toReal := ENNReal.toReal_nonneg
    rw [abs_sub_le_iff]; constructor <;> linarith
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, mul_one]
    have : IsProbabilityMeasure (iterKernel P (n₀ * 0) ∘ₘ Q) := by
      constructor; rw [comp_apply_univ_of_isMarkov, measure_univ]
    exact (hbound1 _ this).trans (by linarith)
  · set n := n₀ * k with hn
    have hn1 : 1 ≤ n := by rw [hn]; nlinarith
    -- write the difference as an integral
    have hmeas : Measurable (fun x => ((iterKernel P n x) C).toReal) :=
      (Kernel.measurable_coe _ hC).ennreal_toReal
    have hbdd : ∀ x, ((iterKernel P n x) C).toReal ≤ 1 := fun x => by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    have hint : Integrable (fun x => ((iterKernel P n x) C).toReal) Q := by
      refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]; exact hbdd x
    have heq : ((iterKernel P n ∘ₘ Q) C).toReal = ∫ x, ((iterKernel P n x) C).toReal ∂Q := by
      rw [Measure.bind_apply hC (Kernel.aemeasurable _)]
      rw [integral_toReal (Kernel.measurable_coe _ hC).aemeasurable
        (Filter.Eventually.of_forall (fun x => measure_lt_top _ _))]
    have hc : (π C).toReal = ∫ _x, (π C).toReal ∂Q := by simp
    rw [heq, hc, ← integral_sub hint (integrable_const _)]
    have hae : ∀ᵐ x ∂Q, ‖((iterKernel P n x) C).toReal - (π C).toReal‖ ≤ KQ * t ^ n := by
      filter_upwards [hrateQ n hn1] with x hx
      rw [Real.norm_eq_abs]
      exact (abs_toReal_sub_le_tvDist _ _ hC).trans hx
    have := norm_integral_le_of_norm_le_const hae
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
    calc |∫ x, (((iterKernel P n x) C).toReal - (π C).toReal) ∂Q|
        ≤ KQ * t ^ n := this
      _ = KQ * (t ^ n₀) ^ k := by rw [hn, pow_mul]
      _ ≤ (KQ + 1) * (t ^ n₀) ^ k := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end rates

section drift

variable (P : Kernel X X) [IsMarkovKernel P] (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (C : Set X)
  (hC : MeasurableSet C) (ε : ℝ) (hε : 0 < ε) (Q : Measure X) [IsProbabilityMeasure Q]
  (hmin : ∀ x ∈ C, ∀ A, MeasurableSet A → ENNReal.ofReal ε * Q A ≤ (iterKernel P n₀) x A)
  (π : Measure X) [IsProbabilityMeasure π] (hπC : 0 < π C) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
  (KQ : ℝ) (hKQ : 0 ≤ KQ)
  (hrateQ : ∀ n, 1 ≤ n → ∀ᵐ x ∂Q, tvDist (iterKernel P n x) π ≤ KQ * t ^ n)
  (Mt : X → ℝ) (hMt0 : ∀ x, 0 ≤ Mt x)
  (hrate : ∀ x, ∀ n, 1 ≤ n → tvDist (iterKernel P n x) π ≤ Mt x * t ^ n)

include hn₀ hC hε hπC ht0 ht1 hKQ hrateQ hMt0 hrate in
/-- **uniform geometric bound on the no-regeneration probability**, for every start `P^j(x,·)`
and for `Q`. -/
theorem residual_bound :
    ∃ r C₀ : ℝ, 1 < r ∧ 0 ≤ C₀ ∧
      (∀ x j k, ((iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ iterKernel P j x) Set.univ).toReal
        ≤ C₀ * (1 + ε * (Mt x + 1)) * r⁻¹ ^ k) ∧
      (∀ k, ((iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ Q) Set.univ).toReal
        ≤ C₀ * (1 + ε * (KQ + 1)) * r⁻¹ ^ k) := by
  have hε' : 0 ≤ ε := hε.le
  have hL : 0 < ε * (π C).toReal := mul_pos hε (ENNReal.toReal_pos hπC.ne' (measure_ne_top _ _))
  have hρ0 : 0 ≤ t ^ n₀ := pow_nonneg ht0 _
  have hρ1 : t ^ n₀ < 1 := pow_lt_one₀ ht0 ht1 (by omega)
  obtain ⟨r, C₀, hr1, hC₀, hpkg⟩ := renewal_package
    (Bseq P n₀ C hC ε Q hmin Q) (Wseq P n₀ C ε Q) (rseq P n₀ C hC ε Q hmin Q)
    (ε * (π C).toReal) (ε * (KQ + 1)) (t ^ n₀) hL (mul_nonneg hε' (by linarith)) hρ0 hρ1
    (Bseq_nonneg P n₀ C hC ε Q hmin Q hε')
    (fun k => Wseq_eq P n₀ C hC ε Q hmin Q hε' k)
    (fun k => Wseq_conv_Q P n₀ hn₀ C hC ε hε' Q π t ht0 ht1 KQ hKQ hrateQ k)
    (by unfold rseq; rw [iterKernel_zero, id_comp_measure, measure_univ, ENNReal.toReal_one])
    (rseq_nonneg P n₀ C hC ε Q hmin Q)
    (fun m => rseq_succ P n₀ C hC ε Q hmin Q hε' m)
    (fun k => rseq_eq P n₀ C hC ε Q hmin Q hε' k)
  refine ⟨r, C₀, hr1, hC₀, ?_, ?_⟩
  · intro x j k
    have := hpkg (Wseq P n₀ C ε (iterKernel P j x)) (Bseq P n₀ C hC ε Q hmin (iterKernel P j x))
      (rseq P n₀ C hC ε Q hmin (iterKernel P j x)) (ε * (Mt x + 1))
      (mul_nonneg hε' (by linarith [hMt0 x]))
      (fun k => Wseq_conv_iter P n₀ hn₀ C hC ε hε' π t ht0 ht1 x j (Mt x) (hMt0 x) (hrate x) k)
      (fun k => Wseq_eq P n₀ C hC ε Q hmin _ hε' k)
      (Bseq_nonneg P n₀ C hC ε Q hmin _ hε') (rseq_nonneg P n₀ C hC ε Q hmin _)
      (fun m => rseq_succ P n₀ C hC ε Q hmin _ hε' m)
      (fun k => rseq_eq P n₀ C hC ε Q hmin _ hε' k) k
    exact this
  · intro k
    have := hpkg (Wseq P n₀ C ε Q) (Bseq P n₀ C hC ε Q hmin Q) (rseq P n₀ C hC ε Q hmin Q)
      (ε * (KQ + 1)) (mul_nonneg hε' (by linarith))
      (fun k => Wseq_conv_Q P n₀ hn₀ C hC ε hε' Q π t ht0 ht1 KQ hKQ hrateQ k)
      (fun k => Wseq_eq P n₀ C hC ε Q hmin Q hε' k)
      (Bseq_nonneg P n₀ C hC ε Q hmin Q hε') (rseq_nonneg P n₀ C hC ε Q hmin Q)
      (fun m => rseq_succ P n₀ C hC ε Q hmin Q hε' m)
      (fun k => rseq_eq P n₀ C hC ε Q hmin Q hε' k) k
    exact this

/-- the skeleton drift function `W(x) = ∑_k κ₁^k (R^k 1)(x)`, in `ℝ≥0∞`. -/
noncomputable def Wf (κ₁ : ℝ) (x : X) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (κ₁ ^ k) * (iterKernel (Rres P n₀ C hC ε Q hmin) k x Set.univ)

lemma measurable_Wf (κ₁ : ℝ) : Measurable (Wf P n₀ C hC ε Q hmin κ₁) := by
  unfold Wf
  refine Measurable.ennreal_tsum (fun k => ?_)
  exact (Kernel.measurable_coe _ MeasurableSet.univ).const_mul _

/-- `∫ W dμ = ∑_k κ₁^k (R^k μ)(X)`. -/
lemma lintegral_Wf (κ₁ : ℝ) (μ : Measure X) :
    ∫⁻ x, Wf P n₀ C hC ε Q hmin κ₁ x ∂μ =
      ∑' k : ℕ, ENNReal.ofReal (κ₁ ^ k) * (iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ μ) Set.univ := by
  unfold Wf
  rw [lintegral_tsum (fun k => ((Kernel.measurable_coe _ MeasurableSet.univ).const_mul _).aemeasurable)]
  refine tsum_congr (fun k => ?_)
  rw [lintegral_const_mul _ (Kernel.measurable_coe _ MeasurableSet.univ),
    Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]

/-- bound on `∫ W dμ` from a geometric bound on the residual mass. -/
lemma lintegral_Wf_le (κ₁ r D : ℝ) (hκ₁0 : 0 ≤ κ₁) (hκ₁r : κ₁ < r) (hr : 0 < r) (hD : 0 ≤ D)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hbound : ∀ k, ((iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ μ) Set.univ).toReal ≤ D * r⁻¹ ^ k) :
    ∫⁻ x, Wf P n₀ C hC ε Q hmin κ₁ x ∂μ ≤ ENNReal.ofReal (D / (1 - κ₁ / r)) := by
  rw [lintegral_Wf]
  have hq0 : 0 ≤ κ₁ / r := by positivity
  have hq1 : κ₁ / r < 1 := (div_lt_one hr).2 hκ₁r
  have hterm : ∀ k, ENNReal.ofReal (κ₁ ^ k) * (iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ μ) Set.univ
      ≤ ENNReal.ofReal (D * (κ₁ / r) ^ k) := by
    intro k
    have hfin := Rk_comp_ne_top P n₀ C hC ε Q hmin μ k Set.univ
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc κ₁ ^ k * ((iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ μ) Set.univ).toReal
        ≤ κ₁ ^ k * (D * r⁻¹ ^ k) := mul_le_mul_of_nonneg_left (hbound k) (by positivity)
      _ = D * (κ₁ / r) ^ k := by rw [div_eq_mul_inv, mul_pow]; ring
  calc ∑' k, ENNReal.ofReal (κ₁ ^ k) * (iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ μ) Set.univ
      ≤ ∑' k, ENNReal.ofReal (D * (κ₁ / r) ^ k) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' k, D * (κ₁ / r) ^ k) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          ((summable_geometric_of_lt_one hq0 hq1).mul_left D)]
    _ = ENNReal.ofReal (D / (1 - κ₁ / r)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv D]

end drift


section skeleton

variable (P : Kernel X X) [IsMarkovKernel P] (n₀ : ℕ) (C : Set X)
  (hC : MeasurableSet C) (ε : ℝ) (hε : 0 ≤ ε) (Q : Measure X) [IsProbabilityMeasure Q]
  (hmin : ∀ x ∈ C, ∀ A, MeasurableSet A → ENNReal.ofReal ε * Q A ≤ (iterKernel P n₀) x A)

lemma iterKernel_succ' (κ : Kernel X X) (k : ℕ) : iterKernel κ (k + 1) = iterKernel κ k ∘ₖ κ := by
  rw [iterKernel_add, iterKernel_succ, iterKernel_zero, Kernel.comp_id]

/-- `∫ W dR(x,·)`: shifting the sum by one. -/
lemma lintegral_Wf_Rres (κ₁ : ℝ) (hκ₁ : 0 ≤ κ₁) (x : X) :
    ENNReal.ofReal κ₁ * ∫⁻ y, Wf P n₀ C hC ε Q hmin κ₁ y ∂(Rres P n₀ C hC ε Q hmin x) + 1
      = Wf P n₀ C hC ε Q hmin κ₁ x := by
  rw [lintegral_Wf, ← ENNReal.tsum_mul_left]
  unfold Wf
  have hshift : (∑' k : ℕ, ENNReal.ofReal (κ₁ ^ k) * (iterKernel (Rres P n₀ C hC ε Q hmin) k x Set.univ))
      = ENNReal.ofReal (κ₁ ^ 0) * (iterKernel (Rres P n₀ C hC ε Q hmin) 0 x Set.univ) +
        ∑' k : ℕ, ENNReal.ofReal (κ₁ ^ (k + 1)) * (iterKernel (Rres P n₀ C hC ε Q hmin) (k + 1) x Set.univ) :=
    tsum_eq_zero_add' ENNReal.summable
  rw [hshift]
  simp only [pow_zero, ENNReal.ofReal_one, one_mul, iterKernel_zero, Kernel.id_apply, measure_univ]
  rw [add_comm]
  congr 1
  refine tsum_congr (fun k => ?_)
  have : iterKernel (Rres P n₀ C hC ε Q hmin) k ∘ₘ Rres P n₀ C hC ε Q hmin x
      = iterKernel (Rres P n₀ C hC ε Q hmin) (k + 1) x := by
    rw [iterKernel_succ', Kernel.comp_apply]
  rw [this, ← mul_assoc, ← ENNReal.ofReal_mul hκ₁, pow_succ, mul_comm κ₁]

include hε in
/-- **skeleton drift identity**: `κ₁ ∫ W dP^{n₀}(x,·) + 1 = W(x) + κ₁ ε 1_C(x) ∫ W dQ`. -/
theorem skeleton_drift (κ₁ : ℝ) (hκ₁ : 0 ≤ κ₁) (x : X) :
    ENNReal.ofReal κ₁ * ∫⁻ y, Wf P n₀ C hC ε Q hmin κ₁ y ∂(iterKernel P n₀ x) + 1
      = Wf P n₀ C hC ε Q hmin κ₁ x +
        ENNReal.ofReal κ₁ * (C.indicator (fun _ => ENNReal.ofReal ε) x *
          ∫⁻ y, Wf P n₀ C hC ε Q hmin κ₁ y ∂Q) := by
  have hsplit : iterKernel P n₀ x = Rres P n₀ C hC ε Q hmin x + Ereg C hC ε Q x := by
    rw [← Rres_add_Ereg P n₀ C hC ε Q hmin, Kernel.add_apply]
  rw [hsplit, lintegral_add_measure, mul_add, add_right_comm, lintegral_Wf_Rres P n₀ C hC ε Q hmin κ₁ hκ₁,
    Ereg_apply, lintegral_smul_measure, smul_eq_mul]

end skeleton


section final

variable (P : Kernel X X) [IsMarkovKernel P] (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (C : Set X)
  (hC : MeasurableSet C) (ε : ℝ) (hε : 0 < ε) (Q : Measure X) [IsProbabilityMeasure Q]
  (hmin : ∀ x ∈ C, ∀ A, MeasurableSet A → ENNReal.ofReal ε * Q A ≤ (iterKernel P n₀) x A)
  (π : Measure X) [IsProbabilityMeasure π] (hπC : 0 < π C) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
  (KQ : ℝ) (hKQ : 0 ≤ KQ)
  (hrateQ : ∀ n, 1 ≤ n → ∀ᵐ x ∂Q, tvDist (iterKernel P n x) π ≤ KQ * t ^ n)
  (Mt : X → ℝ) (hMt0 : ∀ x, 0 ≤ Mt x)
  (hrate : ∀ x, ∀ n, 1 ≤ n → tvDist (iterKernel P n x) π ≤ Mt x * t ^ n)

include hn₀ hC hε hmin hπC ht0 ht1 hKQ hrateQ hMt0 hrate in
/-- **the geometric drift condition from regeneration.** -/
theorem exists_geoDrift :
    ∃ V : X → ℝ, Measurable V ∧ (∀ x, 1 ≤ V x) ∧
      ∃ d b : ℝ, 0 < d ∧ GeoDriftCondition P V d b C := by
  obtain ⟨r, C₀, hr1, hC₀, hbx, hbQ⟩ := residual_bound P n₀ hn₀ C hC ε hε Q hmin π hπC t ht0 ht1
    KQ hKQ hrateQ Mt hMt0 hrate
  have hr0 : 0 < r := by linarith
  have hrinv0 : 0 < r⁻¹ := by positivity
  have hrinv1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  -- the contraction factor `μ` and `κ₁ = μ^{-n₀} < r`
  set δ := (1 - r⁻¹) / (2 * n₀) with hδ
  have hn₀' : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hδ0 : 0 < δ := by rw [hδ]; apply div_pos <;> linarith
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set μ := 1 - δ with hμ
  have hμ0 : 0 < μ := by rw [hμ]; linarith
  have hμ1 : μ < 1 := by rw [hμ]; linarith
  have hμn : r⁻¹ < μ ^ n₀ := by
    have hb := one_add_mul_le_pow (a := -δ) (by linarith) n₀
    have hn₀ne : (n₀ : ℝ) ≠ 0 := by positivity
    have h1 : (n₀ : ℝ) * δ = (1 - r⁻¹) / 2 := by
      rw [hδ]; field_simp; try ring
    have : 1 + (n₀ : ℝ) * (-δ) = (1 + r⁻¹) / 2 := by
      rw [mul_neg, h1]; ring
    rw [this] at hb
    have hμeq : (1 + -δ) = μ := by rw [hμ]; try ring
    calc r⁻¹ < (1 + r⁻¹) / 2 := by linarith
      _ ≤ (1 + -δ) ^ n₀ := hb
      _ = μ ^ n₀ := by rw [hμeq]
  set κ₁ := (μ ^ n₀)⁻¹ with hκ₁
  have hμn0 : 0 < μ ^ n₀ := by positivity
  have hκ₁0 : 0 < κ₁ := by positivity
  have hκ₁r : κ₁ < r := by
    rw [hκ₁, inv_lt_comm₀ hμn0 hr0]; exact hμn
  have hκ₁eq : κ₁ = μ⁻¹ ^ n₀ := by rw [hκ₁, inv_pow]
  -- the skeleton drift function and its integrals
  set W := Wf P n₀ C hC ε Q hmin κ₁ with hW
  have hWmeas : Measurable W := measurable_Wf P n₀ C hC ε Q hmin κ₁
  have hq0 : 0 ≤ κ₁ / r := by positivity
  have hq1 : κ₁ / r < 1 := (div_lt_one hr0).2 hκ₁r
  have hDen : 0 < 1 - κ₁ / r := by linarith
  -- finiteness of `∫ W dP^j(x,·)`
  have hWfin : ∀ x j, ∫⁻ y, W y ∂(iterKernel P j x) ≠ ⊤ := by
    intro x j
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_Wf_le P n₀ C hC ε Q hmin κ₁ r (C₀ * (1 + ε * (Mt x + 1))) hκ₁0.le hκ₁r hr0
        (by have := hMt0 x; positivity) (iterKernel P j x) (fun k => hbx x j k))
  have hWQfin : ∫⁻ y, W y ∂Q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_Wf_le P n₀ C hC ε Q hmin κ₁ r (C₀ * (1 + ε * (KQ + 1))) hκ₁0.le hκ₁r hr0
        (by positivity) Q hbQ)
  set qW := (∫⁻ y, W y ∂Q).toReal with hqW
  have hqW0 : 0 ≤ qW := ENNReal.toReal_nonneg
  -- real integrals of `W`
  set w : X → ℕ → ℝ := fun x j => (∫⁻ y, W y ∂(iterKernel P j x)).toReal with hw
  have hw0 : ∀ x, w x 0 = (W x).toReal := by
    intro x
    simp only [hw, iterKernel_zero, Kernel.id_apply]
    rw [lintegral_dirac' _ hWmeas]
  have hwnn : ∀ x j, 0 ≤ w x j := fun x j => ENNReal.toReal_nonneg
  have hWxfin : ∀ x, W x ≠ ⊤ := by
    intro x
    have := hWfin x 0
    simpa [iterKernel_zero, Kernel.id_apply, lintegral_dirac' _ hWmeas] using this
  have hW1 : ∀ x, 1 ≤ (W x).toReal := by
    intro x
    have h1 : (1 : ℝ≥0∞) ≤ W x := by
      have := ENNReal.le_tsum (f := fun k => ENNReal.ofReal (κ₁ ^ k) *
        (iterKernel (Rres P n₀ C hC ε Q hmin) k x Set.univ)) 0
      simpa [iterKernel_zero, Kernel.id_apply] using this
    have := ENNReal.toReal_mono (hWxfin x) h1
    simpa using this
  -- measurability of `w · j`
  have hwmeas : ∀ j, Measurable (fun x => w x j) := fun j =>
    ((Measure.measurable_lintegral hWmeas).comp (Kernel.measurable _)).ennreal_toReal
  -- the skeleton drift, in reals
  have hskel : ∀ x, κ₁ * w x n₀ + 1 = w x 0 + κ₁ * (C.indicator (fun _ => ε) x * qW) := by
    intro x
    have h := skeleton_drift P n₀ C hC ε hε.le Q hmin κ₁ hκ₁0.le x
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hWfin x n₀)) ENNReal.one_ne_top,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ₁0.le, ENNReal.toReal_one,
      ENNReal.toReal_add (hWxfin x) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (by
          by_cases hx : x ∈ C <;> simp [hx]) hWQfin)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ₁0.le, ENNReal.toReal_mul] at h'
    rw [hw0]
    convert h' using 4
    by_cases hx : x ∈ C <;> simp [hx, ENNReal.toReal_ofReal hε.le]
  -- `∫ w(·, j) dP(x,·) = w(x, j+1)` and integrability
  have hlint : ∀ x j, ∫⁻ y, ∫⁻ z, W z ∂(iterKernel P j y) ∂(P x) = ∫⁻ z, W z ∂(iterKernel P (j + 1) x) := by
    intro x j
    rw [iterKernel_succ', Kernel.lintegral_comp _ _ _ hWmeas]
  have hmj : ∀ j, Measurable (fun y => ∫⁻ z, W z ∂(iterKernel P j y)) := fun j =>
    (Measure.measurable_lintegral hWmeas).comp (Kernel.measurable _)
  have hint : ∀ x j, ∫ y, w y j ∂(P x) = w x (j + 1) := by
    intro x j
    simp only [hw]
    rw [integral_toReal (hmj j).aemeasurable
      (Filter.Eventually.of_forall (fun y => lt_top_iff_ne_top.2 (hWfin y j))), hlint]
  have hinteg : ∀ x j, Integrable (fun y => w y j) (P x) := by
    intro x j
    refine integrable_toReal_of_lintegral_ne_top (hmj j).aemeasurable ?_
    rw [hlint]; exact hWfin x (j + 1)
  -- the drift function
  set V : X → ℝ := fun x => ∑ j ∈ range n₀, μ⁻¹ ^ j * w x j with hV
  refine ⟨V, ?_, ?_, 1 - μ, μ * κ₁ * ε * qW, by linarith, ?_, ?_⟩
  · exact Finset.measurable_sum _ (fun j _ => (hwmeas j).const_mul _)
  · intro x
    have h0 : 0 ∈ range n₀ := mem_range.2 (by omega)
    calc (1 : ℝ) ≤ w x 0 := by rw [hw0]; exact hW1 x
      _ = μ⁻¹ ^ 0 * w x 0 := by simp
      _ ≤ ∑ j ∈ range n₀, μ⁻¹ ^ j * w x j :=
          Finset.single_le_sum (fun j _ => mul_nonneg (by positivity) (hwnn x j)) h0
  · intro x
    exact integrable_finset_sum _ (fun j _ => (hinteg x j).const_mul _)
  · intro x
    have hintV : ∫ y, V y ∂(P x) = ∑ j ∈ range n₀, μ⁻¹ ^ j * w x (j + 1) := by
      simp only [hV]
      rw [integral_finset_sum _ (fun j _ => (hinteg x j).const_mul _)]
      refine sum_congr rfl (fun j _ => ?_)
      rw [integral_const_mul, hint]
    have halg : ∑ j ∈ range n₀, μ⁻¹ ^ j * w x (j + 1)
        = μ * (V x + κ₁ * w x n₀ - w x 0) := by
      have h1 : ∑ j ∈ range n₀, μ⁻¹ ^ j * w x (j + 1)
          = μ * ∑ j ∈ range n₀, μ⁻¹ ^ (j + 1) * w x (j + 1) := by
        rw [mul_sum]
        refine sum_congr rfl (fun j _ => ?_)
        rw [pow_succ]
        field_simp
      have h2 : ∑ j ∈ range n₀, μ⁻¹ ^ (j + 1) * w x (j + 1)
          = ∑ j ∈ range (n₀ + 1), μ⁻¹ ^ j * w x j - w x 0 := by
        rw [sum_range_succ' (fun j => μ⁻¹ ^ j * w x j) n₀]
        simp
      have h3 : ∑ j ∈ range (n₀ + 1), μ⁻¹ ^ j * w x j = V x + κ₁ * w x n₀ := by
        rw [sum_range_succ, hκ₁eq]
      rw [h1, h2, h3]
    have hskel' := hskel x
    have hind : C.indicator (fun _ => ε) x = ε * C.indicator (fun _ => (1 : ℝ)) x := by
      by_cases hx : x ∈ C <;> simp [hx]
    rw [hintV, halg]
    rw [hind] at hskel'
    nlinarith [hμ0, hκ₁0, hqW0, hwnn x n₀, hwnn x 0, hskel', hε]

end final


end Regen
end

section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT Regen

namespace Regen

lemma tvDist_nonneg'' {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : 0 ≤ tvDist μ ν := by
  unfold tvDist
  apply Real.sSup_nonneg
  rintro r ⟨A, _, rfl⟩
  exact abs_nonneg _

/-- **Meyn–Tweedie 15.0.1, (i) ⇒ (iii)** on a countably generated space, via regeneration. -/
theorem geoDrift_main {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π) :
    ∃ V : X → ℝ, Measurable V ∧ (∀ x, 1 ≤ V x) ∧
      ∃ C : Set X, MeasurableSet C ∧ IsSmallSet P C ∧
        ∃ d b : ℝ, 0 < d ∧ GeoDriftCondition P V d b C := by
  obtain ⟨M, t, hM0, ht0, ht1, hrate⟩ := hgeo
  -- a positive rate
  set t' := max t (1 / 2) with ht'
  have ht'0 : 0 < t' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have ht'1 : t' < 1 := max_lt ht1 (by norm_num)
  have htt' : t ≤ t' := le_max_left _ _
  have hrate' : ∀ x n, 1 ≤ n → tvDist (iterKernel P n x) π ≤ M x * t' ^ n := fun x n hn =>
    (hrate x n hn).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 htt' n) (hM0 x))
  -- the measurable rate constant `Mt`
  set Mt : X → ℝ := fun x => ⨆ n : ℕ, tvDist (iterKernel P (n + 1) x) π / t' ^ (n + 1) with hMt
  have hbdd : ∀ x, BddAbove (Set.range (fun n : ℕ => tvDist (iterKernel P (n + 1) x) π / t' ^ (n + 1))) := by
    intro x
    refine ⟨M x, ?_⟩
    rintro r ⟨n, rfl⟩
    rw [div_le_iff₀ (by positivity)]
    exact hrate' x (n + 1) (by omega)
  have hMt0 : ∀ x, 0 ≤ Mt x := fun x =>
    Real.iSup_nonneg (fun n => div_nonneg (tvDist_nonneg'' _ _) (by positivity))
  have hrateMt : ∀ x n, 1 ≤ n → tvDist (iterKernel P n x) π ≤ Mt x * t' ^ n := by
    intro x n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := le_ciSup (hbdd x) m
    rw [div_le_iff₀ (by positivity)] at this
    exact this
  have hMtmeas : Measurable Mt := by
    refine Measurable.iSup (fun n => ?_)
    exact (measurable_tvDist_kernel (iterKernel P (n + 1)) π).div_const _
  -- a small set of positive measure
  obtain ⟨C, hCm, hCsmall, hπC⟩ := exists_isSmallSet_measure_pos P π hP ⟨M, t, hM0, ht0, ht1, hrate⟩
  obtain ⟨n₀, hn₀, ε, hε, Q, hQ, hmin⟩ := hCsmall
  haveI := hQ
  -- shrink `Q` to a level set of `Mt`
  set S : ℕ → Set X := fun K => {x | Mt x ≤ K} with hS
  have hSmeas : ∀ K, MeasurableSet (S K) := fun K => measurableSet_le hMtmeas measurable_const
  have hSunion : (⋃ K, S K) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, hS, Set.mem_setOf_eq]
    exact exists_nat_ge (Mt x)
  obtain ⟨KQ, hKQ⟩ : ∃ K, Q (S K) ≠ 0 := by
    by_contra h
    push_neg at h
    have : Q (⋃ K, S K) = 0 := measure_iUnion_null_iff.2 h
    rw [hSunion, measure_univ] at this
    exact one_ne_zero this
  have hQS_top : Q (S KQ) ≠ ⊤ := measure_ne_top _ _
  set Q' : Measure X := (Q (S KQ))⁻¹ • Q.restrict (S KQ) with hQ'
  haveI hQ'prob : IsProbabilityMeasure Q' := by
    constructor
    rw [hQ', Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      smul_eq_mul, ENNReal.inv_mul_cancel hKQ hQS_top]
  set ε' := ε * (Q (S KQ)).toReal with hε'
  have hQSpos : 0 < (Q (S KQ)).toReal := ENNReal.toReal_pos hKQ hQS_top
  have hε'pos : 0 < ε' := mul_pos hε hQSpos
  have hmin' : ∀ x ∈ C, ∀ A, MeasurableSet A → ENNReal.ofReal ε' * Q' A ≤ (iterKernel P n₀) x A := by
    intro x hx A hA
    rw [hQ', Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul, hε',
      ENNReal.ofReal_mul hε.le, ENNReal.ofReal_toReal hQS_top]
    calc ENNReal.ofReal ε * Q (S KQ) * ((Q (S KQ))⁻¹ * Q (A ∩ S KQ))
        = ENNReal.ofReal ε * Q (A ∩ S KQ) := by
          rw [mul_assoc, ← mul_assoc (Q (S KQ)), ENNReal.mul_inv_cancel hKQ hQS_top, one_mul]
      _ ≤ ENNReal.ofReal ε * Q A :=
          mul_le_mul_left' (measure_mono Set.inter_subset_left) _
      _ ≤ (iterKernel P n₀) x A := hmin x hx A hA
  have hrateQ : ∀ n, 1 ≤ n → ∀ᵐ x ∂Q', tvDist (iterKernel P n x) π ≤ (KQ : ℝ) * t' ^ n := by
    intro n hn
    have hmem : ∀ᵐ x ∂Q', x ∈ S KQ := by
      rw [hQ']
      exact Measure.ae_smul_measure (ae_restrict_mem (hSmeas KQ)) _
    filter_upwards [hmem] with x hx
    simp only [hS, Set.mem_setOf_eq] at hx
    calc tvDist (iterKernel P n x) π ≤ Mt x * t' ^ n := hrateMt x n hn
      _ ≤ (KQ : ℝ) * t' ^ n := mul_le_mul_of_nonneg_right hx (by positivity)
  -- the drift function
  obtain ⟨V, hVm, hV1, d, b, hd, hdrift⟩ := exists_geoDrift P n₀ hn₀ C hCm ε' hε'pos Q' hmin' π hπC
    t' ht'0.le ht'1 (KQ : ℝ) (Nat.cast_nonneg _) hrateQ Mt hMt0 hrateMt
  exact ⟨V, hVm, hV1, C, hCm, ⟨n₀, hn₀, ε', hε'pos, Q', hQ'prob, hmin'⟩, d, b, hd, hdrift⟩

end Regen
end

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π) :
    ∃ V : X → ℝ, Measurable V ∧ (∀ x, 1 ≤ V x) ∧
      ∃ C : Set X, MeasurableSet C ∧ IsSmallSet P C ∧
        ∃ d b : ℝ, 0 < d ∧ GeoDriftCondition P V d b C :=
  Regen.geoDrift_main P π hP hgeo
