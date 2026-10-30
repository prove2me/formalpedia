-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.erdos_limit_constant_of_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:18:15.118554+00:00
-- url     : https://prove2.me/submissions/0719de6e-e4e7-40b1-9e2c-75bbc0d07406

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_EulerProduct
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_LaplaceLimit
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_LaplaceAsymptotic
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosConstant
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions

open scoped BigOperators

lemma part_pos (n : ℕ) : 0 < part n := by
  dsimp [part]
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨Nat.Partition.indiscrete n⟩

lemma A_pos : 0 < A := by
  dsimp [A]
  positivity

lemma A_nonneg : 0 ≤ A := A_pos.le

lemma log_one_div_le_self {u : ℝ} (hu : 0 < u) :
    Real.log (1 + 1 / u) ≤ 1 / u := by
  have hpos : 0 < 1 + 1 / u := by positivity
  have := Real.log_le_sub_one_of_pos hpos
  linarith

lemma neg_log_one_sub_le_tsum {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    -Real.log (1 - y) = ∑' j : ℕ, y ^ (j + 1) / ((j : ℝ) + 1) := by
  have habs : |y| < 1 := by simpa [abs_of_nonneg hy0] using hy1
  exact (Real.hasSum_pow_div_log_of_abs_lt_one habs).tsum_eq.symm

lemma hasSum_one_div_nat_succ_sq :
    HasSum (fun j : ℕ => (1 : ℝ) / (((j : ℝ) + 1) ^ 2)) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' (G := ℝ)
    (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
  simpa [pow_two, add_comm, add_left_comm, add_assoc] using h

lemma tsum_one_div_nat_succ_sq :
    (∑' j : ℕ, (1 : ℝ) / (((j : ℝ) + 1) ^ 2)) = A := by
  simpa [A] using hasSum_one_div_nat_succ_sq.tsum_eq

lemma geom_ratio_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {m : ℕ} (hm : 0 < m) :
    x ^ m / (1 - x ^ m) ≤ x / ((m : ℝ) * (1 - x)) := by
  have hx0' : 0 ≤ x := hx0.le
  have hx1' : x ≤ 1 := hx1.le
  have hpow_lt_one : x ^ m < 1 := pow_lt_one₀ hx0' hx1 hm.ne'
  have hden_pos : 0 < 1 - x ^ m := sub_pos.mpr hpow_lt_one
  have hsmall_pos : 0 < (m : ℝ) * x ^ (m - 1) * (1 - x) := by
    have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have hxpow : 0 < x ^ (m - 1) := pow_pos hx0 _
    have hxden : 0 < 1 - x := sub_pos.mpr hx1
    positivity
  have hsum_lower :
      (m : ℝ) * x ^ (m - 1) ≤ ∑ i ∈ Finset.range m, x ^ i := by
    calc
      (m : ℝ) * x ^ (m - 1) = ∑ i ∈ Finset.range m, x ^ (m - 1) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range m, x ^ i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi_le : i ≤ m - 1 := Nat.le_pred_of_lt (Finset.mem_range.mp hi)
        exact pow_le_pow_of_le_one hx0' hx1' hi_le
  have hden_lower : (m : ℝ) * x ^ (m - 1) * (1 - x) ≤ 1 - x ^ m := by
    have hmul := mul_le_mul_of_nonneg_right hsum_lower (sub_nonneg.mpr hx1')
    simpa [geom_sum_mul_of_le_one hx1' m, mul_assoc] using hmul
  calc
    x ^ m / (1 - x ^ m) ≤ x ^ m / ((m : ℝ) * x ^ (m - 1) * (1 - x)) := by
      exact div_le_div_of_nonneg_left (pow_nonneg hx0' m) hsmall_pos hden_lower
    _ = x / ((m : ℝ) * (1 - x)) := by
      rw [show x ^ m = x ^ (m - 1) * x by
        rw [← pow_succ, Nat.sub_add_cancel hm]]
      field_simp [hx0.ne', (Nat.cast_pos.mpr hm).ne', sub_ne_zero.mpr hx1.ne]

lemma finite_partition_log_product_bound {n : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (∑ i ∈ Finset.range n, -Real.log (1 - x ^ (i + 1))) ≤ A * x / (1 - x) := by
  classical
  let f : ℕ → ℕ → ℝ := fun i j =>
    (x ^ (i + 1)) ^ (j + 1) / ((j : ℝ) + 1)
  have hx0' : 0 ≤ x := hx0.le
  have hx1' : x ≤ 1 := hx1.le
  have hf_sum : ∀ i ∈ Finset.range n, Summable (f i) := by
    intro i hi
    have hpow_nonneg : 0 ≤ x ^ (i + 1) := pow_nonneg hx0' _
    have hpow_lt : x ^ (i + 1) < 1 := pow_lt_one₀ hx0' hx1 (Nat.succ_ne_zero i)
    exact (Real.hasSum_pow_div_log_of_abs_lt_one
      (by simpa [abs_of_nonneg hpow_nonneg] using hpow_lt)).summable
  have hlog_eq :
      (∑ i ∈ Finset.range n, -Real.log (1 - x ^ (i + 1)))
        = ∑' j : ℕ, ∑ i ∈ Finset.range n, f i j := by
    rw [Summable.tsum_finsetSum hf_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hpow_nonneg : 0 ≤ x ^ (i + 1) := pow_nonneg hx0' _
    have hpow_lt : x ^ (i + 1) < 1 := pow_lt_one₀ hx0' hx1 (Nat.succ_ne_zero i)
    exact neg_log_one_sub_le_tsum hpow_nonneg hpow_lt
  have hmajor_hasSum :
      HasSum (fun j : ℕ => x / (((j : ℝ) + 1) ^ 2 * (1 - x)))
        (A * x / (1 - x)) := by
    have h := hasSum_one_div_nat_succ_sq.mul_left (x / (1 - x))
    convert h using 1
    · ext j
      field_simp [pow_two, sub_ne_zero.mpr hx1.ne]
    · simp [A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hlog_eq]
  have hbound :
      ∀ j : ℕ, (∑ i ∈ Finset.range n, f i j)
        ≤ x / (((j : ℝ) + 1) ^ 2 * (1 - x)) := by
    intro j
    have hm_pos : 0 < j + 1 := Nat.succ_pos j
    have hpowm_lt : x ^ (j + 1) < 1 := pow_lt_one₀ hx0' hx1 hm_pos.ne'
    have hgeom :
        HasSum (fun i : ℕ => (x ^ (j + 1)) ^ (i + 1) / ((j : ℝ) + 1))
          (x ^ (j + 1) / (1 - x ^ (j + 1)) / ((j : ℝ) + 1)) := by
      have hbase :
          HasSum (fun i : ℕ => (x ^ (j + 1)) ^ (i + 1))
            (x ^ (j + 1) / (1 - x ^ (j + 1))) := by
        let r := x ^ (j + 1)
        have hr_nonneg : 0 ≤ r := pow_nonneg hx0' _
        have hr_lt : r < 1 := by simpa [r] using hpowm_lt
        have hgeo := (hasSum_nat_add_iff' (G := ℝ)
          (f := fun i : ℕ => r ^ i) 1).mpr
          (hasSum_geometric_of_lt_one hr_nonneg hr_lt)
        have hgeo' : HasSum (fun i : ℕ => r ^ (i + 1)) (r / (1 - r)) := by
          convert hgeo using 1
          simp only [Finset.sum_range_one, pow_zero]
          have hden : 1 - r ≠ 0 := by linarith
          field_simp [hden]
          ring
        simpa [r] using hgeo'
      simpa [div_eq_mul_inv, mul_assoc] using hbase.mul_right (((j : ℝ) + 1)⁻¹)
    have hgeom_f :
        HasSum (fun i : ℕ => f i j)
          (x ^ (j + 1) / (1 - x ^ (j + 1)) / ((j : ℝ) + 1)) := by
      convert hgeom using 1
      funext i
      dsimp [f]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    calc
      (∑ i ∈ Finset.range n, f i j)
          ≤ x ^ (j + 1) / (1 - x ^ (j + 1)) / ((j : ℝ) + 1) := by
        refine sum_le_hasSum (Finset.range n) ?_ hgeom_f
        intro i hi
        dsimp [f]
        positivity
      _ ≤ x / (((j : ℝ) + 1) ^ 2 * (1 - x)) := by
        have hratio := geom_ratio_le hx0 hx1 hm_pos
        have hratio' :
            x ^ (j + 1) / (1 - x ^ (j + 1))
              ≤ x / (((j : ℝ) + 1) * (1 - x)) := by
          simpa using hratio
        have hden_nonneg : 0 ≤ ((j : ℝ) + 1)⁻¹ := by positivity
        calc
          x ^ (j + 1) / (1 - x ^ (j + 1)) / ((j : ℝ) + 1)
              = (x ^ (j + 1) / (1 - x ^ (j + 1))) * (((j : ℝ) + 1)⁻¹) := by
                ring
          _ ≤ (x / (((j : ℝ) + 1) * (1 - x))) * (((j : ℝ) + 1)⁻¹) := by
                exact mul_le_mul_of_nonneg_right hratio' hden_nonneg
          _ = x / (((j : ℝ) + 1) ^ 2 * (1 - x)) := by
                field_simp [pow_two]
  have hsumm_left : Summable (fun j : ℕ => ∑ i ∈ Finset.range n, f i j) :=
    Summable.of_nonneg_of_le
      (fun j => by
        refine Finset.sum_nonneg ?_
        intro i hi
        dsimp [f]
        positivity)
      hbound
      hmajor_hasSum.summable
  exact hasSum_le hbound hsumm_left.hasSum hmajor_hasSum

lemma partition_range_count_sum (n : ℕ) (p : Nat.Partition n) :
    (∑ i ∈ Finset.range n, p.parts.count (i + 1) * (i + 1)) = n := by
  have hIcc :
      (∑ m ∈ Finset.Icc 1 n, p.parts.count m * m) = n := by
    have hmem := Nat.Partition.toFinsuppAntidiag_mem_finsuppAntidiag (p := p)
    have hsum := (Finset.mem_finsuppAntidiag.mp hmem).1
    simpa [Nat.Partition.toFinsuppAntidiag, mul_comm] using hsum
  calc
    (∑ i ∈ Finset.range n, p.parts.count (i + 1) * (i + 1))
        = ∑ m ∈ Finset.Icc 1 n, p.parts.count m * m := by
      refine Finset.sum_bij (fun i hi => i + 1) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_Icc]
        constructor
        · exact Nat.succ_pos i
        · exact Finset.mem_range.mp hi
      · intro a ha b hb h
        exact Nat.succ.inj h
      · intro b hb
        rw [Finset.mem_Icc] at hb
        refine ⟨b - 1, ?_, ?_⟩
        · rw [Finset.mem_range]
          omega
        · exact Nat.sub_add_cancel hb.1
      · intro i hi
        rfl
    _ = n := hIcc

lemma partition_count_le_n {n i : ℕ} (p : Nat.Partition n) (hi : i ∈ Finset.range n) :
    p.parts.count (i + 1) ≤ n := by
  have hterm :
      p.parts.count (i + 1) * (i + 1) ≤ n := by
    have hsingle :
        p.parts.count (i + 1) * (i + 1)
          ≤ ∑ k ∈ Finset.range n, p.parts.count (k + 1) * (k + 1) := by
      exact Finset.single_le_sum
        (s := Finset.range n)
        (f := fun k => p.parts.count (k + 1) * (k + 1))
        (fun k hk => Nat.zero_le _) hi
    simpa [partition_range_count_sum n p] using hsingle
  have hcount_le :
      p.parts.count (i + 1) ≤ p.parts.count (i + 1) * (i + 1) := by
    nth_rewrite 1 [← Nat.mul_one (p.parts.count (i + 1))]
    exact Nat.mul_le_mul_left _ (Nat.succ_pos i)
  exact hcount_le.trans hterm

lemma partition_product_term_eq {n : ℕ} (z : ℝ) (p : Nat.Partition n) :
    (∏ a ∈ (Finset.range n).attach,
        z ^ ((a.1 + 1) * p.parts.count (a.1 + 1))) = z ^ n := by
  calc
    (∏ a ∈ (Finset.range n).attach,
        z ^ ((a.1 + 1) * p.parts.count (a.1 + 1)))
        = ∏ i ∈ Finset.range n, z ^ ((i + 1) * p.parts.count (i + 1)) := by
      simpa using
        (Finset.prod_attach (Finset.range n)
          (fun i => z ^ ((i + 1) * p.parts.count (i + 1))))
    _ = z ^ (∑ i ∈ Finset.range n, (i + 1) * p.parts.count (i + 1)) := by
      exact Finset.prod_pow_eq_pow_sum (Finset.range n)
        (fun i => (i + 1) * p.parts.count (i + 1)) z
    _ = z ^ n := by
      congr 1
      simpa [Nat.mul_comm] using partition_range_count_sum n p

lemma partition_multiplicity_injective (n : ℕ) :
    Function.Injective
      (fun p : Nat.Partition n =>
        fun i : ℕ => fun _hi : i ∈ Finset.range n => p.parts.count (i + 1)) := by
  intro p q h
  apply Nat.Partition.ext
  apply Multiset.ext.mpr
  intro m
  by_cases hm0 : m = 0
  · subst hm0
    have hp0 : 0 ∉ p.parts := by
      intro hp
      exact (Nat.not_lt_zero _) (p.parts_pos hp)
    have hq0 : 0 ∉ q.parts := by
      intro hq
      exact (Nat.not_lt_zero _) (q.parts_pos hq)
    simp [Multiset.count_eq_zero_of_notMem hp0, Multiset.count_eq_zero_of_notMem hq0]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    by_cases hmn : m ≤ n
    · have hi : m - 1 ∈ Finset.range n := by
        rw [Finset.mem_range]
        omega
      have hval := congr_fun (congr_fun h (m - 1)) hi
      simpa [Nat.sub_add_cancel hmpos] using hval
    · have hpmn : m ∉ p.parts := by
        intro hp
        exact hmn (Nat.Partition.le_of_mem_parts hp)
      have hqmn : m ∉ q.parts := by
        intro hq
        exact hmn (Nat.Partition.le_of_mem_parts hq)
      simp [Multiset.count_eq_zero_of_notMem hpmn, Multiset.count_eq_zero_of_notMem hqmn]

lemma partition_le_truncated_product {n : ℕ} {z : ℝ} (hz0 : 0 ≤ z) :
    part n * z ^ n
      ≤ ∏ i ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1), z ^ ((i + 1) * j) := by
  classical
  let enc : Nat.Partition n → (i : ℕ) → i ∈ Finset.range n → ℕ :=
    fun p i _hi => p.parts.count (i + 1)
  let term : ((i : ℕ) → i ∈ Finset.range n → ℕ) → ℝ :=
    fun q => ∏ a ∈ (Finset.range n).attach, z ^ ((a.1 + 1) * q a.1 a.2)
  have henc_mem :
      ∀ p : Nat.Partition n, enc p ∈ (Finset.range n).pi (fun _ => Finset.range (n + 1)) := by
    intro p
    rw [Finset.mem_pi]
    intro i hi
    rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (partition_count_le_n p hi)
  have henc_inj : Set.InjOn enc (Finset.univ : Finset (Nat.Partition n)) := by
    intro p _ q _ hpq
    exact partition_multiplicity_injective n hpq
  have hterm_enc : ∀ p : Nat.Partition n, term (enc p) = z ^ n := by
    intro p
    dsimp [term, enc]
    exact partition_product_term_eq z p
  have hleft :
      part n * z ^ n = ∑ p : Nat.Partition n, term (enc p) := by
    simp [part, hterm_enc, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have himage_subset :
      Finset.image enc (Finset.univ : Finset (Nat.Partition n))
        ⊆ (Finset.range n).pi (fun _ => Finset.range (n + 1)) := by
    intro q hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨p, _hp, rfl⟩
    exact henc_mem p
  calc
    part n * z ^ n = ∑ p : Nat.Partition n, term (enc p) := hleft
    _ = ∑ q ∈ Finset.image enc (Finset.univ : Finset (Nat.Partition n)), term q := by
      exact (Finset.sum_image henc_inj).symm
    _ ≤ ∑ q ∈ (Finset.range n).pi (fun _ => Finset.range (n + 1)), term q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
        (fun q _hq _hnot => by
          dsimp [term]
          exact Finset.prod_nonneg (fun a _ha => pow_nonneg hz0 _))
    _ = ∏ i ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1), z ^ ((i + 1) * j) := by
      rw [Finset.prod_sum]

lemma partition_log_bound_x (n : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Real.log (part n) ≤ -((n : ℝ) * Real.log z) + A * z / (1 - z) := by
  classical
  have hz0' : 0 ≤ z := hz0.le
  have hcomb := partition_le_truncated_product (n := n) (z := z) hz0'
  let trunc : ℝ := ∏ i ∈ Finset.range n,
    ∑ j ∈ Finset.range (n + 1), z ^ ((i + 1) * j)
  let euler : ℝ := ∏ i ∈ Finset.range n, (1 - z ^ (i + 1))⁻¹
  have hleft_pos : 0 < part n * z ^ n := mul_pos (part_pos n) (pow_pos hz0 n)
  have htrunc_pos : 0 < trunc := by
    dsimp [trunc]
    refine Finset.prod_pos ?_
    intro i hi
    refine Finset.sum_pos' ?_ ?_
    · intro j hj
      exact pow_nonneg hz0' _
    · refine ⟨0, by simp, ?_⟩
      simp
  have htrunc_le_euler : trunc ≤ euler := by
    dsimp [trunc, euler]
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      refine Finset.sum_nonneg ?_
      intro j hj
      exact pow_nonneg hz0' _
    · intro i hi
      have hbase_lt : z ^ (i + 1) < 1 :=
        pow_lt_one₀ hz0' hz1 (Nat.succ_ne_zero i)
      have hgeom := hasSum_geometric_of_lt_one (pow_nonneg hz0' _) hbase_lt
      have hsumle :
          (∑ j ∈ Finset.range (n + 1), (z ^ (i + 1)) ^ j)
            ≤ (1 - z ^ (i + 1))⁻¹ := by
        exact sum_le_hasSum (Finset.range (n + 1))
          (fun j hj => pow_nonneg (pow_nonneg hz0' _) _) hgeom
      simpa [pow_mul] using hsumle
  have hlog_comb :
      Real.log (part n * z ^ n) ≤ Real.log trunc :=
    Real.log_le_log hleft_pos (by simpa [trunc] using hcomb)
  have hlog_trunc_euler : Real.log trunc ≤ Real.log euler :=
    Real.log_le_log htrunc_pos htrunc_le_euler
  have hlog_euler :
      Real.log euler = ∑ i ∈ Finset.range n, -Real.log (1 - z ^ (i + 1)) := by
    dsimp [euler]
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Real.log_inv]
    · intro i hi
      have hbase_lt : z ^ (i + 1) < 1 :=
        pow_lt_one₀ hz0' hz1 (Nat.succ_ne_zero i)
      exact inv_ne_zero (by linarith)
  have hlog_left :
      Real.log (part n * z ^ n) = Real.log (part n) + (n : ℝ) * Real.log z := by
    rw [Real.log_mul (part_pos n).ne' (pow_pos hz0 n).ne']
    rw [Real.log_pow]
  have hmain :
      Real.log (part n) + (n : ℝ) * Real.log z ≤ A * z / (1 - z) := by
    calc
      Real.log (part n) + (n : ℝ) * Real.log z
          = Real.log (part n * z ^ n) := hlog_left.symm
      _ ≤ Real.log trunc := hlog_comb
      _ ≤ Real.log euler := hlog_trunc_euler
      _ = ∑ i ∈ Finset.range n, -Real.log (1 - z ^ (i + 1)) := hlog_euler
      _ ≤ A * z / (1 - z) := finite_partition_log_product_bound hz0 hz1
  linarith

theorem partition_log_upper (n : ℕ) (hn : 0 < n) :
    Real.log (part n) ≤ 2 * Real.sqrt (A * n) := by
  let s : ℝ := Real.sqrt (A * (n : ℝ))
  let y : ℝ := (n : ℝ) / s
  let z : ℝ := y / (1 + y)
  have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnR_nonneg : 0 ≤ (n : ℝ) := hnR_pos.le
  have hs_arg_nonneg : 0 ≤ A * (n : ℝ) := mul_nonneg A_nonneg hnR_nonneg
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos_of_pos (mul_pos A_pos hnR_pos)
  have hs_sq : s ^ 2 = A * (n : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt hs_arg_nonneg
  have hy_pos : 0 < y := by
    dsimp [y]
    exact div_pos hnR_pos hs_pos
  have hz_pos : 0 < z := by
    dsimp [z]
    positivity
  have hz_lt_one : z < 1 := by
    dsimp [z]
    rw [div_lt_one (by positivity : 0 < 1 + y)]
    linarith
  have hz_ratio : z / (1 - z) = y := by
    dsimp [z]
    field_simp [show 1 + y ≠ 0 by positivity]
    ring
  have hzinv : z⁻¹ = 1 + 1 / y := by
    dsimp [z]
    field_simp [hy_pos.ne', show 1 + y ≠ 0 by positivity]
    ring
  have hneglog : -Real.log z = Real.log (1 + 1 / y) := by
    rw [← Real.log_inv, hzinv]
  have hneglog_le : -Real.log z ≤ 1 / y := by
    rw [hneglog]
    exact log_one_div_le_self hy_pos
  have hny : (n : ℝ) / y = s := by
    dsimp [y]
    field_simp [hnR_pos.ne', hs_pos.ne']
  have hAy : A * y = s := by
    dsimp [y]
    field_simp [hs_pos.ne']
    rw [← hs_sq]
  have hopt :
      -((n : ℝ) * Real.log z) + A * z / (1 - z) ≤ 2 * s := by
    calc
      -((n : ℝ) * Real.log z) + A * z / (1 - z)
          = (n : ℝ) * (-Real.log z) + A * (z / (1 - z)) := by ring
      _ ≤ (n : ℝ) * (1 / y) + A * y := by
        rw [hz_ratio]
        exact add_le_add (mul_le_mul_of_nonneg_left hneglog_le hnR_nonneg) le_rfl
      _ = (n : ℝ) / y + A * y := by ring
      _ = 2 * s := by
        rw [hny, hAy]
        ring
  exact (partition_log_bound_x n hz_pos hz_lt_one).trans (by simpa [s] using hopt)

theorem two_sqrt_A_eq (n : ℕ) :
    2 * Real.sqrt (A * n) = Real.pi * Real.sqrt (2 * n / 3) := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hleft_nonneg : 0 ≤ 2 * Real.sqrt (A * n) := by positivity
  have hright_nonneg : 0 ≤ Real.pi * Real.sqrt (2 * n / 3) := by positivity
  have harg_right : 0 ≤ (2 : ℝ) * n / 3 := by positivity
  have hsq :
      (2 * Real.sqrt (A * n)) ^ 2
        = (Real.pi * Real.sqrt (2 * n / 3)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg A_nonneg hn_nonneg)]
    rw [mul_pow, Real.sq_sqrt harg_right]
    simp [A]
    ring
  have habs := (sq_eq_sq_iff_abs_eq_abs
    (2 * Real.sqrt (A * n)) (Real.pi * Real.sqrt (2 * n / 3))).mp hsq
  rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at habs
  exact habs

theorem partition_upper_exp (n : ℕ) :
    part n ≤ Real.exp (Real.pi * Real.sqrt (2 * n / 3)) := by
  by_cases hn : 0 < n
  · have hlog := partition_log_upper n hn
    have hexp : part n ≤ Real.exp (2 * Real.sqrt (A * n)) :=
      (Real.log_le_iff_le_exp (part_pos n)).mp hlog
    rw [two_sqrt_A_eq n] at hexp
    exact hexp
  · have hn0 : n = 0 := by omega
    subst hn0
    simp [part]

end AnalyticCombinatorics.Ch8.Partitions
end

section
namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

lemma two_sqrt_A_mul_le_linear {ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    2 * Real.sqrt (A * x) ≤ ε * x + A / ε := by
  have hleft : 0 ≤ 2 * Real.sqrt (A * x) := by positivity
  have hright : 0 ≤ ε * x + A / ε :=
    add_nonneg (mul_nonneg hε.le hx) (div_nonneg A_nonneg hε.le)
  have hAx : 0 ≤ A * x := mul_nonneg A_nonneg hx
  have hεne : ε ≠ 0 := hε.ne'
  have hsquare : 0 ≤ (ε * x - A / ε) ^ 2 := sq_nonneg _
  refine (sq_le_sq₀ hleft hright).mp ?_
  rw [mul_pow, Real.sq_sqrt hAx]
  rw [← sub_nonneg]
  have hdiff :
      (ε * x + A / ε) ^ 2 - 2 ^ 2 * (A * x) = (ε * x - A / ε) ^ 2 := by
    field_simp [hεne]
    ring_nf
  rwa [hdiff]

theorem partLaplace_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n => part n * Real.exp (-(t * n))) := by
  have ht2 : 0 < t / 2 := by positivity
  have hgeom : Summable (fun n : ℕ => Real.exp (-(t / 2) * (n : ℝ))) := by
    have h := Real.summable_exp_nat_mul_iff.mpr (by linarith : -(t / 2) < 0)
    convert h using 1
    ext n
    ring_nf
  refine (hgeom.mul_left (Real.exp (2 * A / t))).of_norm_bounded ?_
  intro n
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hpart : part n ≤ Real.exp (2 * Real.sqrt (A * n)) := by
    have h := partition_upper_exp n
    convert h using 1
    exact congrArg Real.exp (two_sqrt_A_eq n)
  have hlin : 2 * Real.sqrt (A * (n : ℝ)) ≤ (t / 2) * n + A / (t / 2) :=
    two_sqrt_A_mul_le_linear ht2 hn
  calc
    ‖part n * Real.exp (-(t * n))‖
        = part n * Real.exp (-(t * n)) := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact mul_nonneg (part_pos n).le (Real.exp_pos _).le
    _ ≤ Real.exp (2 * Real.sqrt (A * n)) * Real.exp (-(t * n)) := by
          exact mul_le_mul_of_nonneg_right hpart (Real.exp_pos _).le
    _ = Real.exp (2 * Real.sqrt (A * n) - t * n) := by
          rw [← Real.exp_add]
          ring_nf
    _ ≤ Real.exp (2 * A / t - (t / 2) * n) := by
          refine Real.exp_monotone ?_
          have hAdiv : A / (t / 2) = 2 * A / t := by field_simp [ht.ne']
          linarith
    _ = Real.exp (2 * A / t) * Real.exp (-(t / 2) * n) := by
          rw [← Real.exp_add]
          ring_nf

lemma summable_one_div_pnat_sq :
    Summable (fun j : ℕ+ => (1 : ℝ) / (j : ℝ) ^ 2) := by
  exact
    (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)).mpr
      (by
        simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
          using hasSum_one_div_nat_succ_sq.summable)

lemma tsum_one_div_pnat_sq :
    (∑' j : ℕ+, (1 : ℝ) / (j : ℝ) ^ 2) = A := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)]
  simpa [A, pow_two, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
    using tsum_one_div_nat_succ_sq

lemma exp_sub_one_div_self_tendsto_one :
    Tendsto (fun u : ℝ => (Real.exp u - 1) / u) (𝓝[>] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_exp 0).sub_const 1
  have hslope := h.tendsto_slope_zero_right
  simpa [slope, Real.exp_zero, div_eq_mul_inv, mul_comm] using hslope

lemma exp_ratio_tendsto_one (j : ℕ+) :
    Tendsto
      (fun t : ℝ => (t * (j : ℝ)) / (Real.exp (t * (j : ℝ)) - 1))
      (𝓝[>] 0) (𝓝 1) := by
  have hj : 0 < (j : ℝ) := by exact_mod_cast j.2
  have hmul_nhds :
      Tendsto (fun t : ℝ => t * (j : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hc : Tendsto (fun _t : ℝ => (j : ℝ)) (𝓝[>] 0) (𝓝 (j : ℝ)) :=
      tendsto_const_nhds
    simpa using hid.mul hc
  have hmul_pos : ∀ᶠ t : ℝ in 𝓝[>] 0, t * (j : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos ht hj
  have hmul :
      Tendsto (fun t : ℝ => t * (j : ℝ)) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hmul_nhds, hmul_pos⟩
  have hbase := exp_sub_one_div_self_tendsto_one.comp hmul
  have hinv :
      Tendsto
        (fun t : ℝ => ((Real.exp (t * (j : ℝ)) - 1) / (t * (j : ℝ)))⁻¹)
        (𝓝[>] 0) (𝓝 1) := by
    simpa using hbase.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  refine hinv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have htj : 0 < t * (j : ℝ) := mul_pos ht hj
  have hne : Real.exp (t * (j : ℝ)) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr htj).ne'
  field_simp [hne, htpos.ne', hj.ne']

lemma exp_partition_term_bound {t : ℝ} (ht : 0 < t) (j : ℕ+) :
    0 ≤ t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))
    ∧
    t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))
      ≤ 1 / (j : ℝ) ^ 2 := by
  have hj : 0 < (j : ℝ) := by exact_mod_cast j.2
  have htj : 0 < t * (j : ℝ) := mul_pos ht hj
  have hexp_pos : 0 < Real.exp (t * (j : ℝ)) - 1 := by
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr htj)
  have hden_pos : 0 < (j : ℝ) * (Real.exp (t * (j : ℝ)) - 1) :=
    mul_pos hj hexp_pos
  constructor
  · positivity
  · have hlinear : t * (j : ℝ) ≤ Real.exp (t * (j : ℝ)) - 1 := by
      linarith [Real.add_one_le_exp (t * (j : ℝ))]
    have hden_le :
        (j : ℝ) * (t * (j : ℝ)) ≤ (j : ℝ) * (Real.exp (t * (j : ℝ)) - 1) :=
      mul_le_mul_of_nonneg_left hlinear hj.le
    have hsmall_pos : 0 < (j : ℝ) * (t * (j : ℝ)) := mul_pos hj htj
    calc
      t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))
          ≤ t / ((j : ℝ) * (t * (j : ℝ))) := by
            exact div_le_div_of_nonneg_left ht.le hsmall_pos hden_le
      _ = 1 / (j : ℝ) ^ 2 := by
            field_simp [ht.ne', hj.ne']

lemma exp_partition_term_tendsto (j : ℕ+) :
    Tendsto
      (fun t : ℝ =>
        t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)))
      (𝓝[>] 0)
      (𝓝 (1 / (j : ℝ) ^ 2)) := by
  have hj : 0 < (j : ℝ) := by exact_mod_cast j.2
  have hratio := exp_ratio_tendsto_one j
  have hscaled :
      Tendsto
        (fun t : ℝ =>
          ((j : ℝ) ^ 2)⁻¹ *
            ((t * (j : ℝ)) / (Real.exp (t * (j : ℝ)) - 1)))
        (𝓝[>] 0)
        (𝓝 (((j : ℝ) ^ 2)⁻¹)) := by
    simpa using hratio.const_mul (((j : ℝ) ^ 2)⁻¹)
  have heq :
      (fun t : ℝ =>
        ((j : ℝ) ^ 2)⁻¹ *
          ((t * (j : ℝ)) / (Real.exp (t * (j : ℝ)) - 1)))
        =ᶠ[𝓝[>] 0]
      (fun t : ℝ =>
        t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have htj : 0 < t * (j : ℝ) := mul_pos ht hj
    have hne : Real.exp (t * (j : ℝ)) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr htj).ne'
    field_simp [hne, htpos.ne', hj.ne']
  simpa [one_div] using hscaled.congr' heq

theorem partition_laplace_series_asymptotic :
    Tendsto
      (fun t : ℝ =>
        t * (∑' j : ℕ+, 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))))
      (𝓝[>] 0)
      (𝓝 A) := by
  have hdom :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        ∀ j : ℕ+,
          ‖t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))‖
            ≤ (1 : ℝ) / (j : ℝ) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht j
    have hb := exp_partition_term_bound ht j
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have htend :=
    tendsto_tsum_of_dominated_convergence
      (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun (t : ℝ) (j : ℕ+) =>
        t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)))
      (g := fun j : ℕ+ => (1 : ℝ) / (j : ℝ) ^ 2)
      summable_one_div_pnat_sq
      exp_partition_term_tendsto
      hdom
  have hrewrite :
      (fun t : ℝ =>
        t * (∑' j : ℕ+, 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))))
        = fun t : ℝ =>
          ∑' j : ℕ+, t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := by
    funext t
    calc
      t * (∑' j : ℕ+, 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)))
          = ∑' j : ℕ+,
              t * (1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))) := by
            exact (tsum_mul_left
              (a := t)
              (f := fun j : ℕ+ =>
                1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)))).symm
      _ = ∑' j : ℕ+, t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := by
            congr
            funext j
            ring_nf
  rw [hrewrite]
  have hlimit : (∑' j : ℕ+, ((j : ℝ) ^ 2)⁻¹) = A := by
    simpa [one_div] using tsum_one_div_pnat_sq
  simpa [hlimit] using htend

end AnalyticCombinatorics.Ch8.Partitions
end

section
namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

lemma prod_fin_succ_eq_Icc {M : Type*} [CommMonoid M] (K : ℕ) (f : ℕ → M) :
    (∏ i : Fin K, f (i.1 + 1)) = ∏ k ∈ Finset.Icc 1 K, f k := by
  classical
  rw [Finset.prod_fin_eq_prod_range]
  refine Finset.prod_bij (fun i _hi => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc]
    exact ⟨Nat.succ_pos i, Finset.mem_range.mp hi⟩
  · intro _a _ha _b _hb h
    exact Nat.succ.inj h
  · intro b hb
    rw [Finset.mem_Icc] at hb
    refine ⟨b - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · exact Nat.sub_add_cancel hb.1
  · intro i hi
    have hlt : i < K := Finset.mem_range.mp hi
    simp [hlt]

lemma partsLE_eq_weightFiberCard (K n : ℕ) :
    partsLE K n = weightFiberCard K n := by
  change Fintype.card {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K} =
    @Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = n}
      (weightFiberFintype K n)
  exact @Fintype.card_congr
    {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K}
    {q : Fin K → ℕ // multiplicityWeight K q = n}
    inferInstance
    (weightFiberFintype K n)
    (boundedPartitionEquivCounts K n)

lemma multiplicityWeight_snoc (K : ℕ) (q : Fin K → ℕ) (j : ℕ) :
    multiplicityWeight (K + 1) (Fin.snoc q j) =
      multiplicityWeight K q + (K + 1) * j := by
  dsimp [multiplicityWeight]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last]

lemma ennreal_finite_geom_product_eq_tsum_weight (K : ℕ) (r : ENNReal) :
    (∏ i : Fin K, (1 - r ^ (i.1 + 1))⁻¹) =
      ∑' q : Fin K → ℕ, r ^ multiplicityWeight K q := by
  induction K with
  | zero =>
      simp [multiplicityWeight]
  | succ K ih =>
      calc
        (∏ i : Fin (K + 1), (1 - r ^ (i.1 + 1))⁻¹)
            = (∏ i : Fin K, (1 - r ^ (i.1 + 1))⁻¹) * (1 - r ^ (K + 1))⁻¹ := by
                rw [Fin.prod_univ_castSucc]
                simp [Fin.val_last]
        _ = (∑' q : Fin K → ℕ, r ^ multiplicityWeight K q) *
              (∑' j : ℕ, r ^ ((K + 1) * j)) := by
                rw [ih]
                rw [← ENNReal.tsum_geometric (r ^ (K + 1))]
                congr
                ext j
                rw [pow_mul]
        _ = ∑' q : Fin K → ℕ, ∑' j : ℕ,
              r ^ multiplicityWeight K q * r ^ ((K + 1) * j) := by
                rw [← ENNReal.tsum_mul_right]
                congr
                ext q
                rw [← ENNReal.tsum_mul_left]
        _ = ∑' z : (Fin K → ℕ) × ℕ,
              r ^ multiplicityWeight K z.1 * r ^ ((K + 1) * z.2) := by
                rw [(ENNReal.tsum_prod).symm]
        _ = ∑' q : Fin (K + 1) → ℕ, r ^ multiplicityWeight (K + 1) q := by
                rw [← (finSuccFunctionEquiv K).tsum_eq
                  (fun q : Fin (K + 1) → ℕ => r ^ multiplicityWeight (K + 1) q)]
                congr
                ext z
                change r ^ multiplicityWeight K z.1 * r ^ ((K + 1) * z.2) =
                  r ^ multiplicityWeight (K + 1) (Fin.snoc z.1 z.2)
                rw [multiplicityWeight_snoc, pow_add]

lemma ennreal_tsum_weight_group_card (K : ℕ) (r : ENNReal)
    (hfin : ∀ n : ℕ, Fintype {q : Fin K → ℕ // multiplicityWeight K q = n}) :
    (∑' q : Fin K → ℕ, r ^ multiplicityWeight K q) =
      ∑' n : ℕ,
        (@Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = n} (hfin n) : ENNReal)
          * r ^ n := by
  rw [← ENNReal.tsum_fiberwise (fun q : Fin K → ℕ => r ^ multiplicityWeight K q)
    (multiplicityWeight K)]
  congr
  ext n
  letI : Fintype {q : Fin K → ℕ // multiplicityWeight K q = n} := hfin n
  letI : Fintype ↑((multiplicityWeight K) ⁻¹' ({n} : Set ℕ)) :=
    Fintype.ofEquiv _ (weightPreimageEquiv K n).symm
  calc
    (∑' b : ↑((multiplicityWeight K) ⁻¹' ({n} : Set ℕ)), r ^ multiplicityWeight K b.1)
        = ∑' b : ↑((multiplicityWeight K) ⁻¹' ({n} : Set ℕ)), r ^ n := by
            congr
            ext b
            have hb : multiplicityWeight K b.1 = n := b.2
            simp [hb]
    _ = (Fintype.card ↑((multiplicityWeight K) ⁻¹' ({n} : Set ℕ)) : ENNReal) * r ^ n := by
            rw [tsum_fintype]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = (@Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = n} (hfin n) : ENNReal) *
          r ^ n := by
            rw [Fintype.card_congr (weightPreimageEquiv K n)]

lemma ennreal_finite_euler_prod_eq (K : ℕ) (r : ENNReal) :
    (∏ k ∈ Finset.Icc 1 K, (1 - r ^ k)⁻¹) =
      ∑' n : ℕ, (partsLE K n : ENNReal) * r ^ n := by
  rw [← prod_fin_succ_eq_Icc K (fun k : ℕ => (1 - r ^ k)⁻¹)]
  rw [ennreal_finite_geom_product_eq_tsum_weight]
  rw [ennreal_tsum_weight_group_card K r (fun n => weightFiberFintype K n)]
  congr
  ext n
  change (weightFiberCard K n : ENNReal) * r ^ n = (partsLE K n : ENNReal) * r ^ n
  rw [partsLE_eq_weightFiberCard]

lemma partsLE_le_part (K n : ℕ) : (partsLE K n : ℝ) ≤ part n := by
  dsimp [partsLE, part]
  exact_mod_cast (Fintype.card_subtype_le (fun p : Nat.Partition n => ∀ m ∈ p.parts, m ≤ K))

lemma finite_partsLE_summable (K : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => (partsLE K n : ℝ) * x ^ n) := by
  let t : ℝ := -Real.log x
  have ht : 0 < t := by
    dsimp [t]
    exact neg_pos.mpr ((Real.log_neg_iff hx0).mpr hx1)
  have hs := partLaplace_summable (t := t) ht
  refine Summable.of_nonneg_of_le ?_ ?_ hs
  · intro n
    exact mul_nonneg (by positivity) (pow_nonneg hx0.le n)
  · intro n
    have hxpow : Real.exp (-(t * (n : ℝ))) = x ^ n := by
      have harg : -(t * (n : ℝ)) = (n : ℝ) * Real.log x := by
        dsimp [t]
        ring
      rw [harg, Real.exp_nat_mul, Real.exp_log hx0]
    rw [hxpow]
    exact mul_le_mul_of_nonneg_right (partsLE_le_part K n) (pow_nonneg hx0.le n)

theorem finite_euler_prod_eq (K : ℕ) {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    ∏ k ∈ Finset.Icc 1 K, (1 - x^k)⁻¹ = ∑' n : ℕ, (partsLE K n : ℝ) * x^n := by
  have hx0 : 0 ≤ x := h0.le
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ (partsLE K n : ℝ) * x ^ n := by
    intro n
    exact mul_nonneg (by positivity) (pow_nonneg hx0 n)
  have hsum_nonneg : 0 ≤ ∑' n : ℕ, (partsLE K n : ℝ) * x ^ n :=
    tsum_nonneg hterm_nonneg
  have hfactor_nonneg : ∀ k ∈ Finset.Icc 1 K, 0 ≤ (1 - x ^ k)⁻¹ := by
    intro k _hk
    rw [inv_nonneg]
    exact sub_nonneg.mpr (pow_le_one₀ (n := k) hx0 h1.le)
  have hprod_nonneg : 0 ≤ ∏ k ∈ Finset.Icc 1 K, (1 - x ^ k)⁻¹ :=
    Finset.prod_nonneg hfactor_nonneg
  apply (ENNReal.ofReal_eq_ofReal_iff hprod_nonneg hsum_nonneg).mp
  have hL :
      ENNReal.ofReal (∏ k ∈ Finset.Icc 1 K, (1 - x ^ k)⁻¹)
        = ∏ k ∈ Finset.Icc 1 K, (1 - ENNReal.ofReal x ^ k)⁻¹ := by
    rw [ENNReal.ofReal_prod_of_nonneg hfactor_nonneg]
    refine Finset.prod_congr rfl ?_
    intro k hk
    have hxk_nonneg : 0 ≤ x ^ k := pow_nonneg hx0 k
    have hxk_lt : x ^ k < 1 := by
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      exact pow_lt_one₀ hx0 h1 hkpos.ne'
    rw [ENNReal.ofReal_inv_of_pos (sub_pos.mpr hxk_lt)]
    rw [ENNReal.ofReal_sub 1 hxk_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_pow hx0]
  have hsumm := finite_partsLE_summable K h0 h1
  have hR :
      ENNReal.ofReal (∑' n : ℕ, (partsLE K n : ℝ) * x ^ n)
        = ∑' n : ℕ, (partsLE K n : ENNReal) * ENNReal.ofReal x ^ n := by
    rw [ENNReal.ofReal_tsum_of_nonneg hterm_nonneg hsumm]
    congr
    ext n
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (partsLE K n : ℝ))]
    rw [ENNReal.ofReal_natCast, ENNReal.ofReal_pow hx0]
  rw [hL, hR]
  exact ennreal_finite_euler_prod_eq K (ENNReal.ofReal x)

lemma partsLE_eq_part_of_le {K n : ℕ} (h : n ≤ K) :
    (partsLE K n : ℝ) = part n := by
  dsimp [partsLE, part]
  exact_mod_cast Fintype.card_congr (boundedPartitionTopEquiv K n h)

lemma exp_neg_mul_nat_eq_pow (t : ℝ) (n : ℕ) :
    Real.exp (-(t * (n : ℝ))) = Real.exp (-t) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem partLaplace_eq_finprod_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun K : ℕ => ∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹)
      atTop
      (𝓝 (PartLaplace t)) := by
  let x : ℝ := Real.exp (-t)
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    linarith
  have hsum_tendsto :
      Tendsto (fun K : ℕ => ∑' n : ℕ, (partsLE K n : ℝ) * x ^ n)
        atTop (𝓝 (∑' n : ℕ, part n * Real.exp (-(t * (n : ℝ))))) := by
    have hbound_summable : Summable (fun n : ℕ => part n * Real.exp (-(t * (n : ℝ)))) :=
      partLaplace_summable ht
    have hpoint :
        ∀ n : ℕ,
          Tendsto (fun K : ℕ => (partsLE K n : ℝ) * x ^ n)
            atTop (𝓝 (part n * Real.exp (-(t * (n : ℝ))))) := by
      intro n
      refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.mpr ⟨n, ?_⟩
      intro K hK
      change part n * Real.exp (-(t * (n : ℝ))) = (partsLE K n : ℝ) * x ^ n
      rw [partsLE_eq_part_of_le hK, exp_neg_mul_nat_eq_pow]
    have hbound :
        ∀ᶠ K : ℕ in atTop,
          ∀ n : ℕ,
            ‖(partsLE K n : ℝ) * x ^ n‖ ≤ part n * Real.exp (-(t * (n : ℝ))) := by
      refine Eventually.of_forall ?_
      intro K n
      rw [exp_neg_mul_nat_eq_pow]
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact mul_le_mul_of_nonneg_right (partsLE_le_part K n) (pow_nonneg hx0.le n)
      · exact mul_nonneg (by positivity) (pow_nonneg hx0.le n)
    exact tendsto_tsum_of_dominated_convergence hbound_summable hpoint hbound
  refine hsum_tendsto.congr' ?_
  refine Eventually.of_forall ?_
  intro K
  change (∑' n : ℕ, (partsLE K n : ℝ) * x ^ n) =
    ∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹
  rw [← finite_euler_prod_eq K hx0 hx1]
  refine Finset.prod_congr rfl ?_
  intro k hk
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hpow : Real.exp (-(t * (k : ℝ))) = x ^ k := exp_neg_mul_nat_eq_pow t k
  rw [hpow]

end AnalyticCombinatorics.Ch8.Partitions
end

section
namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

-- The log bridge combines finite-product logarithms with several `tsum` reindexing steps.
set_option maxHeartbeats 800000

private lemma PartLaplace_pos {t : ℝ} (ht : 0 < t) :
    0 < PartLaplace t := by
  have hsum := partLaplace_summable ht
  have hnonneg : ∀ n : ℕ, 0 ≤ part n * Real.exp (-(t * (n : ℝ))) := by
    intro n
    exact mul_nonneg (part_pos n).le (Real.exp_pos _).le
  have hzero :
      0 < (fun n : ℕ => part n * Real.exp (-(t * (n : ℝ)))) 0 := by
    exact mul_pos (part_pos 0) (Real.exp_pos _)
  simpa [PartLaplace] using hsum.tsum_pos hnonneg 0 hzero

private lemma exp_neg_mul_pnat_lt_one {t : ℝ} (ht : 0 < t) (k : ℕ+) :
    Real.exp (-(t * (k : ℝ))) < 1 := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast k.2
  have htk : 0 < t * (k : ℝ) := mul_pos ht hk
  rw [Real.exp_lt_one_iff]
  linarith

private lemma neg_log_one_sub_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ -Real.log (1 - y) := by
  exact neg_nonneg.mpr (Real.log_nonpos (sub_nonneg.mpr hy1.le) (by linarith))

private lemma neg_log_one_sub_le_div {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    -Real.log (1 - y) ≤ y / (1 - y) := by
  have hlog := neg_log_one_sub_le_tsum hy0 hy1
  let r : ℝ := y
  have hgeo_tail :
      HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    have hgeo := (hasSum_nat_add_iff' (G := ℝ)
      (f := fun n : ℕ => r ^ n) 1).mpr
      (hasSum_geometric_of_lt_one hy0 hy1)
    convert hgeo using 1
    simp only [Finset.sum_range_one, pow_zero]
    have hden : 1 - r ≠ 0 := by linarith [show r < 1 by simpa [r] using hy1]
    field_simp [hden]
    ring
  have hsumm_log :
      Summable (fun n : ℕ => y ^ (n + 1) / ((n : ℝ) + 1)) := by
    have habs : |y| < 1 := by simpa [abs_of_nonneg hy0] using hy1
    exact (Real.hasSum_pow_div_log_of_abs_lt_one habs).summable
  have hle :
      ∀ n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) ≤ y ^ (n + 1) := by
    intro n
    have hpow : 0 ≤ y ^ (n + 1) := pow_nonneg hy0 _
    have hden : 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    calc
      y ^ (n + 1) / ((n : ℝ) + 1)
          ≤ y ^ (n + 1) / 1 := by
            exact div_le_div_of_nonneg_left hpow zero_lt_one hden
      _ = y ^ (n + 1) := by ring
  rw [hlog]
  exact hasSum_le hle hsumm_log.hasSum hgeo_tail

private lemma summable_logEulerTerm {t : ℝ} (ht : 0 < t) :
    Summable (logEulerTerm t) := by
  let x : ℝ := Real.exp (-t)
  let C : ℝ := (1 - x)⁻¹
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    linarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact inv_nonneg.mpr (sub_nonneg.mpr hx1.le)
  have hgeo_nat : Summable (fun n : ℕ => C * x ^ (n + 1)) := by
    exact ((summable_geometric_of_lt_one hx0 hx1).comp_injective Nat.succ_injective).mul_left C
  have hgeo_pnat : Summable (fun k : ℕ+ => C * x ^ (k : ℕ)) := by
    exact (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => C * x ^ n)).mpr hgeo_nat
  refine Summable.of_nonneg_of_le ?_ ?_ hgeo_pnat
  · intro k
    dsimp [logEulerTerm]
    exact neg_log_one_sub_nonneg (Real.exp_pos _).le (exp_neg_mul_pnat_lt_one ht k)
  · intro k
    dsimp [logEulerTerm]
    have hk : 0 < (k : ℝ) := by exact_mod_cast k.2
    have hpow_eq : Real.exp (-(t * (k : ℝ))) = x ^ (k : ℕ) := by
      rw [exp_neg_mul_nat_eq_pow]
    have hy_le_x : Real.exp (-(t * (k : ℝ))) ≤ x := by
      rw [hpow_eq]
      simpa using (pow_le_pow_of_le_one hx0 hx1.le
        (by exact_mod_cast k.2) : x ^ (k : ℕ) ≤ x ^ 1)
    have hden_le :
        1 - x ≤ 1 - Real.exp (-(t * (k : ℝ))) := by
      exact sub_le_sub_left hy_le_x 1
    calc
      -Real.log (1 - Real.exp (-(t * (k : ℝ))))
          ≤ Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t * (k : ℝ)))) := by
            exact neg_log_one_sub_le_div (Real.exp_pos _).le (exp_neg_mul_pnat_lt_one ht k)
      _ ≤ Real.exp (-(t * (k : ℝ))) / (1 - x) := by
            exact div_le_div_of_nonneg_left (Real.exp_pos _).le (sub_pos.mpr hx1) hden_le
      _ = C * x ^ (k : ℕ) := by
            rw [hpow_eq]
            dsimp [C]
            ring

private lemma summable_logBridgeTerm_right {t : ℝ} (ht : 0 < t) (k : ℕ+) :
    Summable (fun j : ℕ+ => logBridgeTerm t k j) := by
  let y : ℝ := Real.exp (-(t * (k : ℝ)))
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hy1 : y < 1 := by
    dsimp [y]
    exact exp_neg_mul_pnat_lt_one ht k
  have habs : |y| < 1 := by simpa [abs_of_nonneg hy0] using hy1
  have hnat :
      Summable (fun n : ℕ => y ^ (n + 1) / ((n : ℝ) + 1)) :=
    (Real.hasSum_pow_div_log_of_abs_lt_one habs).summable
  have hpnat : Summable (fun j : ℕ+ => y ^ (j : ℕ) / (j : ℝ)) := by
    exact (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => y ^ n / (n : ℝ))).mpr (by
        simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hnat)
  exact hpnat.congr (fun j => by rfl)

private lemma tsum_logBridgeTerm_right {t : ℝ} (ht : 0 < t) (k : ℕ+) :
    (∑' j : ℕ+, logBridgeTerm t k j) = logEulerTerm t k := by
  let y : ℝ := Real.exp (-(t * (k : ℝ)))
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hy1 : y < 1 := by
    dsimp [y]
    exact exp_neg_mul_pnat_lt_one ht k
  have hlog := neg_log_one_sub_le_tsum hy0 hy1
  have hpnat :
      (∑' j : ℕ+, y ^ (j : ℕ) / (j : ℝ)) =
        ∑' n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => y ^ n / (n : ℝ))]
    congr
    funext n
    simp [Nat.cast_add, Nat.cast_one]
  calc
    (∑' j : ℕ+, logBridgeTerm t k j)
        = ∑' j : ℕ+, y ^ (j : ℕ) / (j : ℝ) := by rfl
    _ = ∑' n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) := hpnat
    _ = logEulerTerm t k := by
          dsimp [logEulerTerm, y]
          exact hlog.symm

private lemma tsum_pnat_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' k : ℕ+, r ^ (k : ℕ)) = r / (1 - r) := by
  have hgeo_tail :
      HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    have hgeo := (hasSum_nat_add_iff' (G := ℝ)
      (f := fun n : ℕ => r ^ n) 1).mpr
      (hasSum_geometric_of_lt_one hr0 hr1)
    convert hgeo using 1
    simp only [Finset.sum_range_one, pow_zero]
    have hden : 1 - r ≠ 0 := by linarith
    field_simp [hden]
    ring
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => r ^ n)]
  exact hgeo_tail.tsum_eq

private lemma pow_exp_swap {t : ℝ} (k j : ℕ+) :
    Real.exp (-(t * (k : ℝ))) ^ (j : ℕ) =
      Real.exp (-(t * (j : ℝ))) ^ (k : ℕ) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  ring

private lemma tsum_logBridgeTerm_left {t : ℝ} (ht : 0 < t) (j : ℕ+) :
    (∑' k : ℕ+, logBridgeTerm t k j) =
      1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := by
  let r : ℝ := Real.exp (-(t * (j : ℝ)))
  have hj : 0 < (j : ℝ) := by exact_mod_cast j.2
  have htj : 0 < t * (j : ℝ) := mul_pos ht hj
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  calc
    (∑' k : ℕ+, logBridgeTerm t k j)
        = ∑' k : ℕ+, r ^ (k : ℕ) / (j : ℝ) := by
            refine tsum_congr ?_
            intro k
            dsimp [logBridgeTerm, r]
            rw [pow_exp_swap]
    _ = (∑' k : ℕ+, r ^ (k : ℕ)) / (j : ℝ) := by
            simp_rw [div_eq_mul_inv]
            exact (tsum_mul_right
              (f := fun k : ℕ+ => r ^ (k : ℕ)) (a := (j : ℝ)⁻¹))
    _ = (r / (1 - r)) / (j : ℝ) := by
            rw [tsum_pnat_geometric hr0 hr1]
    _ = 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := by
            dsimp [r]
            rw [Real.exp_neg]
            have hexp_ne : Real.exp (t * (j : ℝ)) ≠ 0 := Real.exp_ne_zero _
            have hsub_ne : Real.exp (t * (j : ℝ)) - 1 ≠ 0 := by
              exact sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr htj).ne'
            field_simp [hj.ne', hexp_ne, hsub_ne]

private lemma logBridgeTerm_nonneg {t : ℝ} (k j : ℕ+) :
    0 ≤ logBridgeTerm t k j := by
  dsimp [logBridgeTerm]
  exact div_nonneg (pow_nonneg (Real.exp_pos _).le _) (by positivity)

private lemma finite_euler_log_eq_sum {t : ℝ} (ht : 0 < t) (K : ℕ) :
    Real.log (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹)
      = ∑ k ∈ Finset.Icc 1 K, -Real.log (1 - Real.exp (-(t * (k : ℝ)))) := by
  have hne :
      ∀ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹ ≠ 0 := by
    intro k hk
    have hkpos_nat : 0 < k := (Finset.mem_Icc.mp hk).1
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkpos_nat
    have htk : 0 < t * (k : ℝ) := mul_pos ht hkpos
    have hexp_lt : Real.exp (-(t * (k : ℝ))) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    exact inv_ne_zero (sub_ne_zero.mpr hexp_lt.ne')
  rw [Real.log_prod hne]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Real.log_inv]

private lemma finite_euler_log_eq_range {t : ℝ} (ht : 0 < t) (K : ℕ) :
    Real.log (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹)
      = ∑ n ∈ Finset.range K, logEulerTerm t (Nat.succPNat n) := by
  calc
    Real.log (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹)
        = ∑ k ∈ Finset.Icc 1 K, -Real.log (1 - Real.exp (-(t * (k : ℝ)))) :=
            finite_euler_log_eq_sum ht K
    _ = ∑ n ∈ Finset.range K, logEulerTerm t (Nat.succPNat n) := by
          symm
          refine Finset.sum_bij (fun n _hn => n + 1) ?_ ?_ ?_ ?_
          · intro n hn
            rw [Finset.mem_Icc]
            exact ⟨Nat.succ_pos n, Finset.mem_range.mp hn⟩
          · intro a ha b hb hab
            exact Nat.succ.inj hab
          · intro b hb
            rw [Finset.mem_Icc] at hb
            refine ⟨b - 1, ?_, ?_⟩
            · rw [Finset.mem_range]
              omega
            · exact Nat.sub_add_cancel hb.1
          · intro n hn
            dsimp [logEulerTerm]

theorem log_partLaplace_eq {t : ℝ} (ht : 0 < t) :
    Real.log (PartLaplace t) =
      ∑' k : ℕ+, -Real.log (1 - Real.exp (-(t * k))) := by
  have hpos : 0 < PartLaplace t := PartLaplace_pos ht
  have hsumm : Summable (logEulerTerm t) := summable_logEulerTerm ht
  have hsucc_summ :
      Summable (fun n : ℕ => logEulerTerm t (Nat.succPNat n)) := by
    exact (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => -Real.log (1 - Real.exp (-(t * (n : ℝ)))))).mp
      (by simpa [logEulerTerm] using hsumm)
  have hpartial :
      Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, logEulerTerm t (Nat.succPNat n))
        atTop (𝓝 (∑' k : ℕ+, logEulerTerm t k)) := by
    have hnat :=
      (hsucc_summ.hasSum.tendsto_sum_nat :
        Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, logEulerTerm t (Nat.succPNat n))
          atTop (𝓝 (∑' n : ℕ, logEulerTerm t (Nat.succPNat n))))
    have htsum :
        (∑' n : ℕ, logEulerTerm t (Nat.succPNat n)) =
          ∑' k : ℕ+, logEulerTerm t k := by
      simpa [Equiv.pnatEquivNat] using
        (Equiv.pnatEquivNat.symm.tsum_eq (fun k : ℕ+ => logEulerTerm t k))
    simpa [htsum] using hnat
  have hlog_tendsto :
      Tendsto
        (fun K : ℕ =>
          Real.log (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹))
        atTop
        (𝓝 (Real.log (PartLaplace t))) := by
    exact (Real.continuousAt_log hpos.ne').tendsto.comp (partLaplace_eq_finprod_tendsto ht)
  have hlog_partial :
      Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, logEulerTerm t (Nat.succPNat n))
        atTop (𝓝 (Real.log (PartLaplace t))) := by
    exact hlog_tendsto.congr' (Eventually.of_forall fun K => finite_euler_log_eq_range ht K)
  have heq : Real.log (PartLaplace t) = ∑' k : ℕ+, logEulerTerm t k :=
    tendsto_nhds_unique hlog_partial hpartial
  simpa [logEulerTerm] using heq

theorem log_series_regroup {t : ℝ} (ht : 0 < t) :
    (∑' k : ℕ+, -Real.log (1 - Real.exp (-(t*k)))) =
      ∑' j : ℕ+, 1 / ((j:ℝ) * (Real.exp (t*j) - 1)) := by
  have hsumm_log : Summable (logEulerTerm t) := summable_logEulerTerm ht
  have hprod_summ :
      Summable (fun p : ℕ+ × ℕ+ => logBridgeTerm t p.1 p.2) := by
    have hrows :
        ∀ k : ℕ+, Summable (fun j : ℕ+ => logBridgeTerm t k j) :=
      summable_logBridgeTerm_right ht
    have hrow_sums :
        Summable (fun k : ℕ+ => ∑' j : ℕ+, logBridgeTerm t k j) := by
      exact hsumm_log.congr (fun k => (tsum_logBridgeTerm_right ht k).symm)
    exact (summable_prod_of_nonneg
      (f := fun p : ℕ+ × ℕ+ => logBridgeTerm t p.1 p.2)
      (fun p => logBridgeTerm_nonneg p.1 p.2)).mpr ⟨hrows, hrow_sums⟩
  calc
    (∑' k : ℕ+, -Real.log (1 - Real.exp (-(t*k))))
        = ∑' k : ℕ+, logEulerTerm t k := by
            simp [logEulerTerm]
    _ = ∑' k : ℕ+, ∑' j : ℕ+, logBridgeTerm t k j := by
            refine tsum_congr ?_
            intro k
            exact (tsum_logBridgeTerm_right ht k).symm
    _ = ∑' j : ℕ+, ∑' k : ℕ+, logBridgeTerm t k j := by
            exact (Summable.tsum_comm hprod_summ).symm
    _ = ∑' j : ℕ+, 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := by
            refine tsum_congr ?_
            intro j
            exact tsum_logBridgeTerm_left ht j

theorem partition_laplace_log_asymptotic :
    Tendsto (fun t : ℝ => t * Real.log (PartLaplace t)) (𝓝[>] 0) (𝓝 A) := by
  refine partition_laplace_series_asymptotic.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [log_partLaplace_eq ht, log_series_regroup ht]

end AnalyticCombinatorics.Ch8.Partitions
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma C_pos : 0 < C := by
  dsimp [C]
  positivity

lemma C_sq_eq_four_mul_A : C ^ 2 = 4 * Partitions.A := by
  dsimp [C, Partitions.A]
  rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 / 3 : ℝ))]
  ring

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

section
/-!
# Mass-rate campaign: Lambert moments — definitions and the central cancellation (R8)

The critical-path brick `|kernelMass n − 1| = O(1/n)` goes through smoothed Lambert
moments `M_r(t) = Σ_m m^r σ(m) e^{−tm}` (NOT a refined pointwise summatory, which cannot
have an `o(x)` secondary at integers because of the `σ(n)` jumps).  This file banks the
definitions, the saddle parameter `λ = C/2` with `λ² = π²/6`, the Bose kernel with its
regularization, and the central algebraic cancellation of the `n^{−1/2}` coefficients:

  `−1/(2λ) + 2Z/λ³ − (C/8)·6Z/λ⁴ = 0`  (`Z = λ²`, `C = 2λ`).

Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The Bose kernel `e^{−x}/(1−e^{−x})²`. -/
noncomputable def boseKernel (x : ℝ) : ℝ :=
  Real.exp (-x) / (1 - Real.exp (-x)) ^ 2

/-- The regularized Bose kernel `boseKernel x − 1/x²` (extends continuously to `−1/12` at 0). -/
noncomputable def boseReg0 (x : ℝ) : ℝ :=
  boseKernel x - 1 / x ^ 2

/-- The Bose kernel is the derivative of `−1/(e^x−1)`: closed antiderivative identity. -/
lemma boseKernel_eq_exp_form {x : ℝ} (hx : 0 < x) :
    boseKernel x = Real.exp x / (Real.exp x - 1) ^ 2 := by
  rw [boseKernel]
  have hexp : Real.exp (-x) = 1 / Real.exp x := by
    rw [Real.exp_neg]
    exact inv_eq_one_div _
  have hepos : 0 < Real.exp x := Real.exp_pos x
  have hne : Real.exp x ≠ 0 := hepos.ne'
  rw [hexp]
  rw [div_eq_div_iff]
  · field_simp
  · have h1 : 1 < Real.exp x := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_lt_exp.mpr hx
    have : 0 < 1 - 1 / Real.exp x := by
      rw [sub_pos, div_lt_one hepos]
      exact h1
    positivity
  · have h1 : 1 < Real.exp x := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_lt_exp.mpr hx
    have : 0 < Real.exp x - 1 := by linarith
    positivity

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: polynomial exponential bounds (R10 bricks 1–3)

Two-sided polynomial bounds for `e^x − 1` on `[0,1]` from `Real.exp_bound` at orders 3, 4 —
the only exp-Taylor input the whole moment package needs.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Order-3 remainder: `|e^x − 1 − x − x²/2| ≤ x³` on `[0,1]`. -/
lemma exp_sub_one_sub_self_sq_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.exp x - 1 - x - x ^ 2 / 2| ≤ x ^ 3 := by
  have habs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    exact hx1
  have h := Real.exp_bound habs (n := 3) (by norm_num)
  have hsum : ∑ i ∈ Finset.range 3, x ^ i / (Nat.factorial i : ℝ)
      = 1 + x + x ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num [Nat.factorial]
  rw [hsum] at h
  have habs3 : |x| ^ 3 = x ^ 3 := by
    rw [abs_of_nonneg hx0]
  rw [habs3] at h
  calc |Real.exp x - 1 - x - x ^ 2 / 2|
      = |Real.exp x - (1 + x + x ^ 2 / 2)| := by ring_nf
    _ ≤ x ^ 3 * ((3 : ℕ).succ / ((Nat.factorial 3 : ℝ) * 3)) := h
    _ ≤ x ^ 3 := by
        have hx3 : (0 : ℝ) ≤ x ^ 3 := by positivity
        have hc : ((3 : ℕ).succ : ℝ) / ((Nat.factorial 3 : ℝ) * 3) ≤ 1 := by
          norm_num [Nat.factorial]
        nlinarith [hx3, hc]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: boseReg0 bounds (R10 bricks 4–6)

The rational form of `boseReg0`, boundedness near zero (`|boseReg0| ≤ 4` on `(0,1]`, via
the exact numerator identity `x²eˣ − (eˣ−1)² = x⁴/4 − 2xδ − δ²` with `|δ| ≤ x³`), and the
tail bound `|boseReg0| ≤ 4e^{−x} + 1/x²` for `x ≥ 1`.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The rational form of `boseReg0` over a common denominator. -/
lemma boseReg0_eq_small_num {x : ℝ} (hx : 0 < x) :
    boseReg0 x = (x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2) /
      (x ^ 2 * (Real.exp x - 1) ^ 2) := by
  have hy : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hypos : 0 < Real.exp x - 1 := by linarith
  rw [boseReg0, boseKernel_eq_exp_form hx]
  field_simp

/-- `|boseReg0| ≤ 4` on `(0,1]`. -/
lemma boseReg0_bdd_near_zero {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |boseReg0 x| ≤ 4 := by
  set δ : ℝ := Real.exp x - 1 - x - x ^ 2 / 2 with hδdef
  have hδ : |δ| ≤ x ^ 3 := by
    rw [hδdef]
    have := exp_sub_one_sub_self_sq_bound hx0.le hx1
    convert this using 2
  have hδlo := (abs_le.mp hδ).1
  have hδhi := (abs_le.mp hδ).2
  have hy : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hypos : 0 < Real.exp x - 1 := by linarith
  -- exact numerator identity
  have hnum_eq : x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2
      = x ^ 4 / 4 - 2 * x * δ - δ ^ 2 := by
    rw [hδdef]
    ring
  have hx3 : x ^ 3 ≤ x ^ 2 := by nlinarith [hx0.le]
  have hnum_abs : |x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2| ≤ 4 * x ^ 4 := by
    rw [hnum_eq, abs_le]
    have hδsq : δ ^ 2 ≤ x ^ 6 := by nlinarith [hδlo, hδhi]
    have hx6 : x ^ 6 ≤ x ^ 4 := by nlinarith [hx0.le, hx1, pow_pos hx0 4]
    have hxδhi : x * δ ≤ x * x ^ 3 := mul_le_mul_of_nonneg_left hδhi hx0.le
    have hxδlo : x * (-(x ^ 3)) ≤ x * δ := mul_le_mul_of_nonneg_left hδlo hx0.le
    constructor
    · nlinarith [hxδhi, hxδlo, hx0.le, hδsq, hx6]
    · nlinarith [hxδhi, hxδlo, hx0.le, hδsq, hx6, sq_nonneg δ]
  have hsq : x ^ 2 ≤ (Real.exp x - 1) ^ 2 := by nlinarith [hy, hx0.le]
  have hden_ge : x ^ 4 ≤ x ^ 2 * (Real.exp x - 1) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ x ^ 2)]
  have hden_pos : 0 < x ^ 2 * (Real.exp x - 1) ^ 2 := by positivity
  rw [boseReg0_eq_small_num hx0, abs_div,
    abs_of_pos hden_pos]
  calc |x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2| / (x ^ 2 * (Real.exp x - 1) ^ 2)
      ≤ (4 * x ^ 4) / x ^ 4 :=
        div_le_div₀ (by positivity) hnum_abs (by positivity) hden_ge
    _ = 4 := by
        field_simp

/-- Tail bound: `|boseReg0 x| ≤ 4e^{−x} + 1/x²` for `x ≥ 1`. -/
lemma boseReg0_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    |boseReg0 x| ≤ 4 * Real.exp (-x) + 1 / x ^ 2 := by
  set_option backward.isDefEq.respectTransparency false in
    have hxpos : (0 : ℝ) < x := by linarith
    have hbose_pos : 0 < boseKernel x := by
      rw [boseKernel]
      have h1 : Real.exp (-x) < 1 := by
        rw [Real.exp_lt_one_iff]
        linarith
      have h2 : 0 < 1 - Real.exp (-x) := by linarith
      positivity
    have hbose_le : boseKernel x ≤ 4 * Real.exp (-x) := by
      rw [boseKernel]
      have hexp1 : Real.exp (-x) ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr
        linarith
      have he1 : Real.exp (-1) ≤ 1 / 2 := by
        have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
        have hprod : Real.exp (-1) * Real.exp 1 = 1 := by
          rw [← Real.exp_add]
          norm_num
        nlinarith [Real.exp_pos (-1),
          mul_le_mul_of_nonneg_left h2e (Real.exp_pos (-1)).le]
      have hden : (1 : ℝ) / 2 ≤ 1 - Real.exp (-x) := by linarith
      have hden_sq : (1 : ℝ) / 4 ≤ (1 - Real.exp (-x)) ^ 2 := by nlinarith
      rw [div_le_iff₀ (by nlinarith : (0:ℝ) < (1 - Real.exp (-x)) ^ 2)]
      nlinarith [Real.exp_pos (-x)]
    have hsplit : |boseReg0 x| ≤ boseKernel x + 1 / x ^ 2 := by
      rw [boseReg0]
      calc |boseKernel x - 1 / x ^ 2|
          ≤ |boseKernel x| + |1 / x ^ 2| := abs_sub _ _
        _ = boseKernel x + 1 / x ^ 2 := by
            rw [abs_of_pos hbose_pos, abs_of_pos (by positivity : (0:ℝ) < 1 / x ^ 2)]
    linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: the Bose antiderivative (R10 bricks 8–12)

`F(x) = 1/x − 1/(eˣ−1)` has `F′ = boseReg0` on `(0,∞)`, `F → 0` at `∞`, `F → 1/2` at `0⁺`
(squeeze via the order-3 bound), with the finite FTC `∫_a^b boseReg0 = F(b) − F(a)`.
Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The antiderivative `1/x − 1/(eˣ−1)`. -/
noncomputable def boseAntideriv (x : ℝ) : ℝ :=
  1 / x - 1 / (Real.exp x - 1)

/-- `F′ = boseReg0` on `(0,∞)`. -/
lemma boseAntideriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt boseAntideriv (boseReg0 x) x := by
  have hy : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hypos : 0 < Real.exp x - 1 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => 1 / x) (-(1 / x ^ 2)) x := by
    have := hasDerivAt_inv hx.ne'
    simpa [one_div] using this
  have hexp : HasDerivAt (fun x : ℝ => Real.exp x - 1) (Real.exp x) x := by
    simpa using (Real.hasDerivAt_exp x).sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => 1 / (Real.exp x - 1))
      (-(Real.exp x / (Real.exp x - 1) ^ 2)) x := by
    have := hexp.inv hypos.ne'
    simpa [one_div, div_eq_mul_inv] using this
  have hsub := h1.sub h2
  have heq : -(1 / x ^ 2) - -(Real.exp x / (Real.exp x - 1) ^ 2) = boseReg0 x := by
    rw [boseReg0, boseKernel_eq_exp_form hx]
    ring
  rw [← heq]
  exact hsub

/-- `boseReg0` is continuous at every `x > 0`. -/
lemma boseReg0_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt boseReg0 x := by
  have hlt : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : (1 - Real.exp (-x)) ^ 2 ≠ 0 := by
    have : 0 < 1 - Real.exp (-x) := by linarith
    positivity
  have hK : ContinuousAt boseKernel x := by
    apply ContinuousAt.div
    · exact (Real.continuous_exp.comp continuous_neg).continuousAt
    · exact ((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).pow 2).continuousAt
    · exact hden
  have hI : ContinuousAt (fun y : ℝ => 1 / y ^ 2) x := by
    apply ContinuousAt.div continuousAt_const ((continuous_pow 2).continuousAt)
    exact pow_ne_zero 2 hx.ne'
  exact hK.sub hI

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Ch8 §VIII — The function `-log(1 - e^{-x})` (toward the HR constant)

Building block for the second-order partition-product asymptotic (DOCTRINE
avenue d, brick 2): `P(e^{-t}) ~ √(t/2π)·e^{A/t}`.  This file isolates the
summand `f(x) = -log(1 - e^{-x})` and its log-regularized form
`h(x) = f(x) + log x`, which removes the logarithmic singularity at `0`
(`h(x) → 0` as `x → 0+`).

These feed the singular Euler–Maclaurin split
`∑_k f(kt) = ∑_k -log(tk) + ∑_k h(kt) + tail` in `ProductSecondOrder.lean`,
where the `√(2π)` constant ultimately comes from Mathlib's Stirling theorem.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Real Filter Topology

/-- `f(x) = -log(1 - e^{-x})`, the Euler-product log summand. -/
noncomputable def log1mexp (x : ℝ) : ℝ := -Real.log (1 - Real.exp (-x))

/-- `h(x) = -log(1 - e^{-x}) + log x`, the log-regularized summand: it removes
the `-log x` singularity of `log1mexp` at `0`, so `h(x) → 0` as `x → 0+`. -/
noncomputable def log1mexpReg (x : ℝ) : ℝ := log1mexp x + Real.log x

/-- For `x > 0`, `1 - e^{-x} > 0`. -/
lemma one_sub_exp_neg_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - Real.exp (-x) := by
  have : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  linarith

/-- `log1mexp` is nonnegative for `x > 0` (since `0 < 1 - e^{-x} ≤ 1`). -/
lemma log1mexp_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ log1mexp x := by
  unfold log1mexp
  have h1 : 1 - Real.exp (-x) ≤ 1 := by
    have : 0 < Real.exp (-x) := Real.exp_pos _
    linarith
  have := Real.log_nonpos (le_of_lt (one_sub_exp_neg_pos hx)) h1
  linarith

/-- Regularized form as a single logarithm: `h(x) = -log((1 - e^{-x})/x)`. -/
lemma log1mexpReg_eq {x : ℝ} (hx : 0 < x) :
    log1mexpReg x = -Real.log ((1 - Real.exp (-x)) / x) := by
  have h1 : 0 < 1 - Real.exp (-x) := one_sub_exp_neg_pos hx
  unfold log1mexpReg log1mexp
  rw [Real.log_div (ne_of_gt h1) (ne_of_gt hx)]
  ring

/-- Tail bound: for `x ≥ log 2`, `|log1mexp x| ≤ 2 e^{-x}` (exponential decay).
Uses `-log(1-y) ≤ y/(1-y) ≤ 2y` for `y = e^{-x} ≤ 1/2`. -/
lemma log1mexp_tail_bound {x : ℝ} (hx : Real.log 2 ≤ x) :
    |log1mexp x| ≤ 2 * Real.exp (-x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num)) hx
  have hle : Real.exp (-x) ≤ 1 / 2 := by
    have hval : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
    have h2 : Real.exp (-x) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    rwa [hval] at h2
  have hy0 : 0 < Real.exp (-x) := Real.exp_pos _
  have h1 : 0 < 1 - Real.exp (-x) := one_sub_exp_neg_pos hx0
  rw [abs_of_nonneg (log1mexp_nonneg hx0)]
  unfold log1mexp
  set y := Real.exp (-x) with hy
  -- Mathlib lower bound: 1 - (1-y)⁻¹ ≤ log(1-y), hence -log(1-y) ≤ (1-y)⁻¹ - 1.
  have hlb : 1 - (1 - y)⁻¹ ≤ Real.log (1 - y) := Real.one_sub_inv_le_log_of_pos h1
  -- eliminate the inverse via w·(1-y) = 1, then (1-y)⁻¹ - 1 ≤ 2y for y ≤ 1/2.
  have hw : (1 - y)⁻¹ * (1 - y) = 1 := inv_mul_cancel₀ (ne_of_gt h1)
  have hwpos : 0 < (1 - y)⁻¹ := inv_pos.mpr h1
  nlinarith [hlb, hw, hwpos, hy0, hle, h1,
    mul_nonneg hy0.le (show (0:ℝ) ≤ 1 - 2 * y by linarith)]

/-- Derivative of `f(x) = -log(1 - e^{-x})` for `x > 0`:
`f'(x) = -e^{-x}/(1 - e^{-x}) = -1/(e^x - 1)`. -/
lemma log1mexp_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt log1mexp (-Real.exp (-x) / (1 - Real.exp (-x))) x := by
  have hpos : 0 < 1 - Real.exp (-x) := one_sub_exp_neg_pos hx
  have hin : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (Real.exp (-x)) x := by
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      have := (Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)
      simpa using this
    simpa using (hasDerivAt_const x (1 : ℝ)).sub h1
  have hout : HasDerivAt (fun y : ℝ => -Real.log y)
      (-(1 - Real.exp (-x))⁻¹) (1 - Real.exp (-x)) :=
    (Real.hasDerivAt_log (ne_of_gt hpos)).neg
  have hcomp := hout.comp x hin
  simpa [log1mexp, div_eq_mul_inv, mul_comm] using hcomp

/-- The regularized summand vanishes at the singularity: `h(x) → 0` as `x → 0+`.
Proof: `h(x) = -log((1 - e^{-x})/x)` and `(1 - e^{-x})/x → 1` (slope of
`x ↦ 1 - e^{-x}` at `0`), so `h(x) → -log 1 = 0`. -/
lemma log1mexpReg_tendsto_zero :
    Tendsto log1mexpReg (𝓝[>] 0) (𝓝 0) := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-1) 0 := by
    have := (Real.hasDerivAt_exp (-0 : ℝ)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg)
    simpa using this
  have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) 1 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub h1
  have hslope : Tendsto (slope (fun x : ℝ => 1 - Real.exp (-x)) 0) (𝓝[≠] 0) (𝓝 1) :=
    hasDerivAt_iff_tendsto_slope.mp hd
  have hratio : Tendsto (fun b : ℝ => (1 - Real.exp (-b)) / b) (𝓝[≠] 0) (𝓝 1) :=
    Filter.Tendsto.congr (fun b => by rw [slope_def_field]; simp [Real.exp_zero]) hslope
  have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono 0 (fun y hy => ne_of_gt hy)
  have hc : Tendsto (fun y : ℝ => Real.log y) (𝓝 1) (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
    simpa using this
  have hlog : Tendsto (fun x : ℝ => -Real.log ((1 - Real.exp (-x)) / x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hc.comp (hratio.mono_left hsub)).neg
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (log1mexpReg_eq hx).symm

end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# `log1mexpReg` has a Lipschitz derivative on `(0,2]` (HR constant, brick 2)

Key reuse (ChatGPT R5): the derivative of `log1mexpReg` on `(0,∞)` is exactly the
repo's Bose antiderivative `boseAntideriv x = 1/x - 1/(e^x-1)`, whose own derivative
is `boseReg0`. The mass-rate development ALREADY proved the hard removable-singularity
bound `|boseReg0| ≤ 4` near `0` (`boseReg0_bdd_near_zero`) plus a tail bound
(`boseReg0_tail_bound`). So `log1mexpReg`'s derivative is `5`-Lipschitz on `(0,2]`
with no new singularity analysis — exactly the `hcell` input the trapezoid machinery
needs (applied on cells `[a,a+h]` with `a > 0`, the head sum starting at `k=1`).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators Interval

noncomputable section

/-- Positive-side derivative of `log1mexpReg` is the Bose antiderivative. -/
lemma log1mexpReg_hasDerivAt_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt log1mexpReg (Erdos.boseAntideriv x) x := by
  have hf := log1mexp_hasDerivAt hx
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  have hraw : HasDerivAt log1mexpReg
      ((-Real.exp (-x) / (1 - Real.exp (-x))) + 1 / x) x := by
    simpa [log1mexpReg] using hf.add hlog
  convert hraw using 1
  rw [Erdos.boseAntideriv, Real.exp_neg]
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have hden : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hx).ne'
  field_simp
  ring

/-- `log1mexpReg` is continuous at positive points. -/
lemma log1mexpReg_continuousAt_pos {x : ℝ} (hx : 0 < x) :
    ContinuousAt log1mexpReg x :=
  (log1mexpReg_hasDerivAt_pos hx).continuousAt

/-- Positive interval-integrability of `log1mexpReg`. -/
lemma log1mexpReg_intervalIntegrable_pos {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable log1mexpReg MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le huv] at hx
  exact (log1mexpReg_continuousAt_pos (lt_of_lt_of_le hu hx.1)).continuousWithinAt

/-- Positive interval-integrability of the derivative `boseAntideriv`. -/
lemma boseAntideriv_intervalIntegrable_pos {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable Erdos.boseAntideriv MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le huv] at hx
  exact (Erdos.boseAntideriv_hasDerivAt
    (lt_of_lt_of_le hu hx.1)).continuousAt.continuousWithinAt

/-- Uniform bound `|boseReg0| ≤ 5` on `(0,2]` (near-zero `≤ 4` + tail `≤ 5`). -/
lemma boseReg0_abs_le_five_Ioc02 {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 2) :
    |Erdos.boseReg0 x| ≤ 5 := by
  by_cases hx1 : x ≤ 1
  · exact le_trans (Erdos.boseReg0_bdd_near_zero hx.1 hx1) (by norm_num)
  · have h1x : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
    have htail := Erdos.boseReg0_tail_bound h1x
    have hexp_le_one : Real.exp (-x) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith [hx.1]
    have hexp_pos : 0 < Real.exp (-x) := Real.exp_pos _
    have hinv_le_one : 1 / x ^ 2 ≤ 1 := by
      have hx2pos : 0 < x ^ 2 := by positivity
      rw [div_le_iff₀ hx2pos]; nlinarith [h1x]
    calc |Erdos.boseReg0 x| ≤ 4 * Real.exp (-x) + 1 / x ^ 2 := htail
      _ ≤ 5 := by nlinarith [hexp_le_one, hinv_le_one, hexp_pos]

/-- `boseAntideriv` (= `log1mexpReg'`) is `5`-Lipschitz on `(0,2]`. -/
lemma boseAntideriv_lipschitz_Ioc02 :
    ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∀ w ∈ Set.Ioc (0 : ℝ) 2,
      |Erdos.boseAntideriv z - Erdos.boseAntideriv w| ≤ 5 * |z - w| := by
  intro z hz w hw
  have hderiv : ∀ x ∈ Set.uIcc z w, HasDerivAt Erdos.boseAntideriv (Erdos.boseReg0 x) x := by
    intro x hx
    have hxpos : 0 < x := by
      rcases le_total z w with hzw | hwz
      · rw [Set.uIcc_of_le hzw] at hx; exact lt_of_lt_of_le hz.1 hx.1
      · rw [Set.uIcc_comm, Set.uIcc_of_le hwz] at hx; exact lt_of_lt_of_le hw.1 hx.1
    exact Erdos.boseAntideriv_hasDerivAt hxpos
  have hcont : ContinuousOn Erdos.boseReg0 (Set.uIcc z w) := by
    intro x hx
    have hxpos : 0 < x := by
      rcases le_total z w with hzw | hwz
      · rw [Set.uIcc_of_le hzw] at hx; exact lt_of_lt_of_le hz.1 hx.1
      · rw [Set.uIcc_comm, Set.uIcc_of_le hwz] at hx; exact lt_of_lt_of_le hw.1 hx.1
    exact (Erdos.boseReg0_continuousAt hxpos).continuousWithinAt
  have hint : IntervalIntegrable Erdos.boseReg0 MeasureTheory.volume z w :=
    hcont.intervalIntegrable
  have hFTC : (∫ x in z..w, Erdos.boseReg0 x) = Erdos.boseAntideriv w - Erdos.boseAntideriv z :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hpoint : ∀ x ∈ Set.uIoc z w, ‖Erdos.boseReg0 x‖ ≤ (5 : ℝ) := by
    intro x hx
    have hxI : x ∈ Set.Ioc (0 : ℝ) 2 := by
      rcases le_total z w with hzw | hwz
      · rw [Set.uIoc_of_le hzw] at hx
        exact ⟨lt_of_lt_of_le hz.1 (le_of_lt hx.1), le_trans hx.2 hw.2⟩
      · rw [Set.uIoc_comm, Set.uIoc_of_le hwz] at hx
        exact ⟨lt_of_lt_of_le hw.1 (le_of_lt hx.1), le_trans hx.2 hz.2⟩
    rw [Real.norm_eq_abs]; exact boseReg0_abs_le_five_Ioc02 hxI
  have hnorm : ‖∫ x in z..w, Erdos.boseReg0 x‖ ≤ (5 : ℝ) * |w - z| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc |Erdos.boseAntideriv z - Erdos.boseAntideriv w|
        = ‖∫ x in z..w, Erdos.boseReg0 x‖ := by rw [hFTC, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ (5 : ℝ) * |w - z| := hnorm
    _ = (5 : ℝ) * |z - w| := by rw [abs_sub_comm]

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# `log1mexpReg` is continuous (hence integrable) on `[0,2]` (HR constant, brick 2)

`log1mexpReg` extends continuously to `0` (value `0`, by `log1mexpReg_tendsto_zero`)
and is continuous on `(0,2]`, so it is `ContinuousOn (Icc 0 2)` and interval-integrable
on every subinterval — discharging the integrability hypothesis of the head theorem.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology
open scoped Topology Interval

noncomputable section

/-- `log1mexpReg` is continuous on `[0,2]` (continuous from the right at `0`,
value `0 = log1mexpReg 0`). -/
lemma log1mexpReg_continuousOn_Icc02 : ContinuousOn log1mexpReg (Set.Icc 0 2) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
  · subst hx0
    have hz : log1mexpReg 0 = 0 := by simp [log1mexpReg, log1mexp]
    rw [← Set.Ioc_insert_left (by norm_num : (0 : ℝ) ≤ 2), continuousWithinAt_insert_self,
      ContinuousWithinAt, hz]
    exact log1mexpReg_tendsto_zero.mono_left (nhdsWithin_mono 0 Set.Ioc_subset_Ioi_self)
  · exact (log1mexpReg_continuousAt_pos hxpos).continuousWithinAt

/-- Interval-integrability of `log1mexpReg` on subintervals of `[0,2]` (`a ≤ b`). -/
lemma log1mexpReg_intervalIntegrable_of_le {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    IntervalIntegrable log1mexpReg MeasureTheory.volume a b := by
  have h : ContinuousOn log1mexpReg (Set.Icc a b) :=
    log1mexpReg_continuousOn_Icc02.mono (Set.Icc_subset_Icc ha hb)
  rw [← Set.uIcc_of_le hab] at h
  exact h.intervalIntegrable

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Ch8 §VIII — Head trapezoid summation brick (toward the HR constant)

The summation/telescoping core for the singular Euler–Maclaurin route (DOCTRINE
avenue d, brick 2).  It assumes a per-cell trapezoid error bound `|cell| ≤ M·h²`
and concludes the head correction tends to `0` (since `N(t)·M·t² ≤ M·t → 0`).

Architecture (per ChatGPT R3): keep the summation brick generic + robust; prove
the per-cell bound separately from the chosen `C²`/Lipschitz-derivative hypothesis
for `log1mexpReg`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators Interval

noncomputable section

/-- Head cutoff `N(t) = ⌊1/t⌋₊`. -/
noncomputable def trapN (t : ℝ) : ℕ := ⌊1 / t⌋₊

/-- Right endpoint `R(t) = N(t)·t`. -/
noncomputable def trapR (t : ℝ) : ℝ := (trapN t : ℝ) * t

/-- Reindex `∑_{k=1}^N f k` as `∑_{k=0}^{N-1} f (k+1)`. -/
lemma sum_Icc_one_eq_sum_range_succ (f : ℕ → ℝ) :
    ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 N, f k) = ∑ k ∈ Finset.range N, f (k + 1) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have htop := Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega) f
      rw [htop, ih]

/-- Telescoping shift identity:
`∑_{k<N} f(k+1) - ∑_{k<N} f(k) = f(N) - f(0)`. -/
lemma sum_range_succ_sub_sum_range (f : ℕ → ℝ) :
    ∀ N : ℕ,
      (∑ k ∈ Finset.range N, f (k + 1)) - (∑ k ∈ Finset.range N, f k) = f N - f 0 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith

/-- Finite exact identity: the right-endpoint sum with endpoint correction equals the
sum of cellwise trapezoid errors (cell `k = [kt, (k+1)t]`). -/
lemma trapezoid_sum_identity_range
    (g : ℝ → ℝ) (t : ℝ) (N : ℕ)
    (hInt : ∀ k ∈ Finset.range N,
        IntervalIntegrable g MeasureTheory.volume
          ((k : ℝ) * t) (((k + 1 : ℕ) : ℝ) * t)) :
    (∑ k ∈ Finset.range N,
        (((g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
          - (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x))
      =
    (∑ k ∈ Finset.range N, g (((k + 1 : ℕ) : ℝ) * t))
      - (1 / t) * (∫ x in (0 : ℝ)..((N : ℝ) * t), g x)
      - (1 / 2) * (g ((N : ℝ) * t) - g 0) := by
  classical
  have hsplit0 :=
    intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) * t) (n := N) (f := g)
      (fun k hk => hInt k (Finset.mem_range.mpr hk))
  have hsplit :
      (∑ k ∈ Finset.range N,
          ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x)
        = ∫ x in (0 : ℝ)..((N : ℝ) * t), g x := by
    simpa using hsplit0
  have hpair :
      (∑ k ∈ Finset.range N,
          (g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
        = (∑ k ∈ Finset.range N, g (((k + 1 : ℕ) : ℝ) * t))
          - (1 / 2) * (g ((N : ℝ) * t) - g 0) := by
    have hshift := sum_range_succ_sub_sum_range (fun k : ℕ => g ((k : ℝ) * t)) N
    simp only [Nat.cast_zero, zero_mul] at hshift
    have hsplit2 :
        (∑ k ∈ Finset.range N, (g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
          = ((∑ k ∈ Finset.range N, g ((k : ℝ) * t))
              + (∑ k ∈ Finset.range N, g (((k + 1 : ℕ) : ℝ) * t))) / 2 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hsplit2]
    linarith
  have hintsum :
      (∑ k ∈ Finset.range N,
          (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x)
        = (1 / t) * (∫ x in (0 : ℝ)..((N : ℝ) * t), g x) := by
    rw [← Finset.mul_sum, hsplit]
  rw [Finset.sum_sub_distrib, hpair, hintsum]
  ring

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Singular head via Stirling (HR constant, brick 2)

The `2π` of the partition prefactor comes from Mathlib's Stirling theorem here.
`singularHead t = ∑_{k=1}^{N t} -log(t·k) = -N log t - log N!`, and
`log N! = N log N - N + ½log(2πN) + o(1)` (from `Stirling.log_stirlingSeq_formula`
+ `tendsto_stirlingSeq_sqrt_pi`). With `R t = N t · t → 1`, this gives

  `singularHead t - [(R - R log R)/t + ½log(t/2π)] → 0`.   (ChatGPT R7)
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators Real
open scoped Topology BigOperators

noncomputable section

/-- `R(t) = ⌊1/t⌋·t → 1` as `t → 0⁺`. -/
lemma trapR_tendsto_one : Tendsto trapR (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h : ∀ᶠ t in 𝓝[>] (0 : ℝ), |trapR t - 1| ≤ t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have hle : ((trapN t : ℝ)) ≤ 1 / t := Nat.floor_le (by positivity)
    have hgt : 1 / t < (trapN t : ℝ) + 1 := Nat.lt_floor_add_one (1 / t)
    have hRle : trapR t ≤ 1 := by
      rw [trapR]
      calc ((trapN t : ℝ)) * t ≤ (1 / t) * t := mul_le_mul_of_nonneg_right hle htpos.le
        _ = 1 := by field_simp
    have hRgt : 1 - t ≤ trapR t := by
      rw [trapR]
      have hlt : (1 / t - 1) * t < ((trapN t : ℝ)) * t :=
        mul_lt_mul_of_pos_right (by linarith) htpos
      have heq : (1 / t - 1) * t = 1 - t := by field_simp
      linarith [heq ▸ hlt]
    rw [abs_le]; constructor <;> linarith
  have hsq : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hzero : Tendsto (fun t => trapR t - 1) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero_norm' (by filter_upwards [h] with t ht; rwa [Real.norm_eq_abs]) hsq
  simpa using hzero.add_const 1

/-- `N(t) = ⌊1/t⌋ → ∞` as `t → 0⁺`. -/
lemma trapN_tendsto_atTop : Tendsto trapN (𝓝[>] (0 : ℝ)) atTop := by
  have hinv : Tendsto (fun t : ℝ => 1 / t) (𝓝[>] (0 : ℝ)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  exact tendsto_nat_floor_atTop.comp hinv

/-- `∑_{k=1}^N log k = log N!`. -/
lemma sum_log_nat_Icc_eq_log_factorial :
    ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 N, Real.log (k : ℝ)) = Real.log (Nat.factorial N : ℝ) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ]
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      push_cast; ring

/-- `singularHead t = ∑_{k=1}^{N t} -log(t·k)`. -/
noncomputable def singularHead (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (trapN t), -Real.log (t * (k : ℝ))

/-- `singularHead t = -(N log t) - log N!` for `t > 0`. -/
lemma singularHead_eq_factorial {t : ℝ} (ht : 0 < t) :
    singularHead t = -((trapN t : ℝ) * Real.log t) - Real.log ((trapN t).factorial : ℝ) := by
  unfold singularHead
  have hterm : ∀ k ∈ Finset.Icc 1 (trapN t),
      -Real.log (t * (k : ℝ)) = -Real.log t - Real.log (k : ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [Real.log_mul (by positivity) (by positivity)]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
    sum_log_nat_Icc_eq_log_factorial, Nat.card_Icc]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- `singularHeadMain t = (R - R log R)/t + ½log(t/2π)`. -/
noncomputable def singularHeadMain (t : ℝ) : ℝ :=
  (trapR t - trapR t * Real.log (trapR t)) / t + (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))

/-- log-factorial Stirling asymptotic along `N(t)`:
`log N! - (N log N - N + ½log(2πN)) → 0`. -/
lemma log_factorial_stirling_along_trapN :
    Tendsto
      (fun t : ℝ =>
        Real.log ((trapN t).factorial : ℝ)
          - ((trapN t : ℝ) * Real.log (trapN t : ℝ) - (trapN t : ℝ)
              + (1 / 2 : ℝ) * Real.log (2 * Real.pi * (trapN t : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Reduce to log (stirlingSeq (trapN t)) - ½ log π → 0.
  have hstir : Tendsto (fun t : ℝ => Real.log (Stirling.stirlingSeq (trapN t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    have hc : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) :=
      (Real.continuousAt_log (by positivity)).tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
    exact hc.comp trapN_tendsto_atTop
  have hlogpi : Real.log (Real.sqrt Real.pi) = (1 / 2 : ℝ) * Real.log Real.pi := by
    rw [Real.log_sqrt Real.pi_pos.le]; ring
  -- Eventually (trapN t ≥ 1) the algebra holds.
  have heventic : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 ≤ trapN t :=
    trapN_tendsto_atTop.eventually_ge_atTop 1
  have hcongr : (fun t : ℝ =>
        Real.log ((trapN t).factorial : ℝ)
          - ((trapN t : ℝ) * Real.log (trapN t : ℝ) - (trapN t : ℝ)
              + (1 / 2 : ℝ) * Real.log (2 * Real.pi * (trapN t : ℝ))))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => Real.log (Stirling.stirlingSeq (trapN t)) - (1 / 2 : ℝ) * Real.log Real.pi) := by
    filter_upwards [heventic] with t ht
    have hN : (1 : ℝ) ≤ (trapN t : ℝ) := by exact_mod_cast ht
    have hNpos : (0 : ℝ) < (trapN t : ℝ) := by linarith
    have hform := Stirling.log_stirlingSeq_formula (trapN t)
    -- log N! = log(stirlingSeq N) + ½ log(2N) + N log(N/e)
    rw [Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp] at hform
    have h2N : Real.log (2 * (trapN t : ℝ)) = Real.log 2 + Real.log (trapN t : ℝ) :=
      Real.log_mul (by norm_num) hNpos.ne'
    have h2piN : Real.log (2 * Real.pi * (trapN t : ℝ))
        = Real.log 2 + Real.log Real.pi + Real.log (trapN t : ℝ) := by
      rw [Real.log_mul (by positivity) hNpos.ne', Real.log_mul (by norm_num) Real.pi_pos.ne']
    rw [h2N] at hform
    rw [h2piN]
    -- hform: log(stirlingSeq N) = log N! - ½(log2+logN) - N(logN - 1)
    nlinarith [hform]
  rw [Filter.tendsto_congr' hcongr]
  have := hstir
  rw [hlogpi] at this
  simpa using this.sub_const ((1 / 2 : ℝ) * Real.log Real.pi)

/-- **Singular head Stirling asymptotic** (the `2π` source):
`singularHead − singularHeadMain = −D − ½ log R → 0` (D from `log_factorial_stirling`,
`R → 1`). -/
theorem singularHead_stirling :
    Tendsto (fun t : ℝ => singularHead t - singularHeadMain t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hD := log_factorial_stirling_along_trapN
  have hR : Tendsto (fun t => Real.log (trapR t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp trapR_tendsto_one
    simpa using this
  have hcomb : Tendsto
      (fun t =>
        -(Real.log ((trapN t).factorial : ℝ)
            - ((trapN t : ℝ) * Real.log (trapN t : ℝ) - (trapN t : ℝ)
                + (1 / 2 : ℝ) * Real.log (2 * Real.pi * (trapN t : ℝ))))
          - (1 / 2 : ℝ) * Real.log (trapR t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hD.neg).sub (hR.const_mul (1 / 2 : ℝ))
    simpa using h
  refine hcomb.congr' ?_
  have heventic : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 ≤ trapN t :=
    trapN_tendsto_atTop.eventually_ge_atTop 1
  filter_upwards [self_mem_nhdsWithin, heventic] with t ht htN
  have htpos : 0 < t := ht
  have hNpos : (0 : ℝ) < (trapN t : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_pos htN
  rw [singularHead_eq_factorial htpos, singularHeadMain, trapR,
    Real.log_mul hNpos.ne' htpos.ne',
    Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hNpos.ne',
    Real.log_div htpos.ne' (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  field_simp
  ring

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Per-cell trapezoid error from a Lipschitz derivative — open-left `(0,2]` version

Variant of `TrapezoidCell.lean`'s producer with hypotheses on `Set.Ioc 0 2`
(derivative need not exist at `0`), for functions like `log1mexpReg` whose
derivative is only defined on `(0,∞)`.  Cells `[a,a+h]` require `0 < a`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators Interval

noncomputable section

private noncomputable def chordI (g : ℝ → ℝ) (a h x : ℝ) : ℝ :=
  ((g (a + h) - g a) / h) * x + (((a + h) * g a - a * g (a + h)) / h)

private lemma chordI_eq_endpoint (g : ℝ → ℝ) {a h x : ℝ} (hh : h ≠ 0) :
    chordI g a h x = ((a + h - x) / h) * g a + ((x - a) / h) * g (a + h) := by
  unfold chordI; field_simp [hh]; ring

private lemma integral_chordI (g : ℝ → ℝ) {a h : ℝ} (hh : h ≠ 0) :
    (∫ x in a..(a + h), chordI g a h x) = h * ((g a + g (a + h)) / 2) := by
  unfold chordI
  set A : ℝ := (g (a + h) - g a) / h with hA
  set B : ℝ := ((a + h) * g a - a * g (a + h)) / h with hB
  have hInt1 : IntervalIntegrable (fun x : ℝ => A * x) MeasureTheory.volume a (a + h) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable (fun _x : ℝ => B) MeasureTheory.volume a (a + h) :=
    continuous_const.intervalIntegrable _ _
  change (∫ x in a..(a + h), A * x + B) = h * ((g a + g (a + h)) / 2)
  rw [intervalIntegral.integral_add hInt1 hInt2, intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const]
  rw [hA, hB]; simp only [smul_eq_mul]; field_simp [hh]; ring

/-- `uIcc x y ⊆ Ioc 0 2` when `x, y ∈ Ioc 0 2`. -/
private lemma uIcc_subset_Ioc02 {x y : ℝ}
    (hxI : x ∈ Set.Ioc (0 : ℝ) 2) (hyI : y ∈ Set.Ioc (0 : ℝ) 2) :
    Set.uIcc x y ⊆ Set.Ioc (0 : ℝ) 2 := by
  intro z hz
  rcases Set.mem_uIcc.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨lt_of_lt_of_le hxI.1 h1, le_trans h2 hyI.2⟩
  · exact ⟨lt_of_lt_of_le hyI.1 h1, le_trans h2 hxI.2⟩

private lemma first_order_error_Ioc
    {g gp : ℝ → ℝ} {M x y : ℝ} (hM : 0 ≤ M)
    (hxI : x ∈ Set.Ioc (0 : ℝ) 2) (hyI : y ∈ Set.Ioc (0 : ℝ) 2)
    (hderiv : ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt g (gp z) z)
    (hint_gp : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → v ≤ 2 →
        IntervalIntegrable gp MeasureTheory.volume u v)
    (hlip : ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∀ w ∈ Set.Ioc (0 : ℝ) 2,
        |gp z - gp w| ≤ M * |z - w|) :
    |g y - g x - (y - x) * gp x| ≤ M * (y - x) ^ 2 := by
  have hsub : Set.uIcc x y ⊆ Set.Ioc (0 : ℝ) 2 := uIcc_subset_Ioc02 hxI hyI
  have hIntGp : IntervalIntegrable gp MeasureTheory.volume x y := by
    rcases le_total x y with hle | hle
    · exact hint_gp hxI.1 hle hyI.2
    · exact (hint_gp hyI.1 hle hxI.2).symm
  have hIntConst : IntervalIntegrable (fun _z : ℝ => gp x) MeasureTheory.volume x y :=
    continuous_const.intervalIntegrable _ _
  have hIntDiff : IntervalIntegrable (fun z : ℝ => gp z - gp x) MeasureTheory.volume x y :=
    hIntGp.sub hIntConst
  have hderivF : ∀ z ∈ Set.uIcc x y,
      HasDerivAt (fun z : ℝ => g z - z * gp x) (gp z - gp x) z := by
    intro z hz
    have hg := hderiv z (hsub hz)
    have hlin : HasDerivAt (fun z : ℝ => z * gp x) (gp x) z := by
      simpa using (hasDerivAt_id z).mul_const (gp x)
    exact hg.sub hlin
  have hFTC : (∫ z in x..y, gp z - gp x) = (g y - y * gp x) - (g x - x * gp x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderivF hIntDiff
  have herr_eq : g y - g x - (y - x) * gp x = ∫ z in x..y, gp z - gp x := by rw [hFTC]; ring
  have hnorm : ‖∫ z in x..y, gp z - gp x‖ ≤ (M * |y - x|) * |y - x| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro z hz
    have hzx : |z - x| ≤ |y - x| ∧ z ∈ Set.Ioc (0 : ℝ) 2 := by
      rcases le_total x y with hle | hle
      · rw [Set.uIoc_of_le hle] at hz
        refine ⟨?_, lt_of_lt_of_le hxI.1 (le_of_lt hz.1), le_trans hz.2 hyI.2⟩
        rw [abs_of_nonneg (by linarith [hz.1] : (0:ℝ) ≤ z - x),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]; linarith [hz.2]
      · rw [Set.uIoc_comm, Set.uIoc_of_le hle] at hz
        refine ⟨?_, lt_of_lt_of_le hyI.1 (le_of_lt hz.1), le_trans hz.2 hxI.2⟩
        rw [abs_of_nonpos (by linarith [hz.2] : z - x ≤ 0),
          abs_of_nonpos (by linarith : y - x ≤ 0)]; linarith [hz.1]
    rw [Real.norm_eq_abs]
    calc |gp z - gp x| ≤ M * |z - x| := hlip z hzx.2 x hxI
      _ ≤ M * |y - x| := mul_le_mul_of_nonneg_left hzx.1 hM
  calc |g y - g x - (y - x) * gp x| = ‖∫ z in x..y, gp z - gp x‖ := by
        rw [herr_eq, Real.norm_eq_abs]
    _ ≤ (M * |y - x|) * |y - x| := hnorm
    _ = M * (y - x) ^ 2 := by rw [mul_assoc, abs_mul_abs_self]; ring

private lemma chordI_error_bound
    {g gp : ℝ → ℝ} {M a h x : ℝ} (hM : 0 ≤ M)
    (hh : 0 < h) (ha : 0 < a) (hb : a + h ≤ 2)
    (hderiv : ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt g (gp z) z)
    (hint_gp : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → v ≤ 2 →
        IntervalIntegrable gp MeasureTheory.volume u v)
    (hlip : ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∀ w ∈ Set.Ioc (0 : ℝ) 2,
        |gp z - gp w| ≤ M * |z - w|)
    (hx : x ∈ Set.Icc a (a + h)) :
    |chordI g a h x - g x| ≤ M * h ^ 2 := by
  have hxa : a ≤ x := hx.1
  have hxb : x ≤ a + h := hx.2
  have hx0 : 0 < x := lt_of_lt_of_le ha hxa
  have hx2 : x ≤ 2 := le_trans hxb hb
  have hxI : x ∈ Set.Ioc (0 : ℝ) 2 := ⟨hx0, hx2⟩
  have haI : a ∈ Set.Ioc (0 : ℝ) 2 := ⟨ha, by linarith⟩
  have habI : a + h ∈ Set.Ioc (0 : ℝ) 2 := ⟨by linarith, hb⟩
  have e1 : |g x - g a - (x - a) * gp x| ≤ M * (x - a) ^ 2 := by
    have hfo := first_order_error_Ioc (g := g) (gp := gp) (M := M)
      (x := x) (y := a) hM hxI haI hderiv hint_gp hlip
    rw [show g x - g a - (x - a) * gp x = -(g a - g x - (a - x) * gp x) by ring, abs_neg,
      show (x - a) ^ 2 = (a - x) ^ 2 by ring]
    exact hfo
  have e2 : |g (a + h) - g x - (a + h - x) * gp x| ≤ M * (a + h - x) ^ 2 :=
    first_order_error_Ioc (g := g) (gp := gp) (M := M) (x := x) (y := a + h)
      hM hxI habI hderiv hint_gp hlip
  have hα : 0 ≤ x - a := sub_nonneg.mpr hxa
  have hβ : 0 ≤ a + h - x := sub_nonneg.mpr hxb
  have hαh : 0 ≤ (x - a) / h := div_nonneg hα hh.le
  have hβh : 0 ≤ (a + h - x) / h := div_nonneg hβ hh.le
  have herr : g x - chordI g a h x =
      ((a + h - x) / h) * (g x - g a - (x - a) * gp x)
        - ((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x) := by
    rw [chordI_eq_endpoint g hh.ne']; field_simp [hh.ne']; ring
  have hterm1 : |((a + h - x) / h) * (g x - g a - (x - a) * gp x)|
        ≤ ((a + h - x) / h) * (M * (x - a) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hβh]; exact mul_le_mul_of_nonneg_left e1 hβh
  have hterm2 : |((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)|
        ≤ ((x - a) / h) * (M * (a + h - x) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hαh]; exact mul_le_mul_of_nonneg_left e2 hαh
  have hmain : |g x - chordI g a h x| ≤ M * (x - a) * (a + h - x) := by
    rw [herr]
    calc |((a + h - x) / h) * (g x - g a - (x - a) * gp x)
            - ((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)|
          ≤ |((a + h - x) / h) * (g x - g a - (x - a) * gp x)|
            + |((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)| := abs_sub _ _
      _ ≤ ((a + h - x) / h) * (M * (x - a) ^ 2)
            + ((x - a) / h) * (M * (a + h - x) ^ 2) := add_le_add hterm1 hterm2
      _ = M * (x - a) * (a + h - x) := by field_simp [hh.ne']; ring
  rw [abs_sub_comm]
  calc |g x - chordI g a h x| ≤ M * (x - a) * (a + h - x) := hmain
    _ ≤ M * h ^ 2 := by
        have hαle : x - a ≤ h := by linarith
        have hβle : a + h - x ≤ h := by linarith
        nlinarith [hM, hα, hβ, hαle, hβle]

/-- Per-cell trapezoid producer, open-left version (cells `[a,a+h]` with `a>0`). -/
theorem cell_trapezoid_bound_of_lipschitz_deriv_Ioc
    {g gp : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt g (gp z) z)
    (hint_g : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → v ≤ 2 →
        IntervalIntegrable g MeasureTheory.volume u v)
    (hint_gp : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → v ≤ 2 →
        IntervalIntegrable gp MeasureTheory.volume u v)
    (hlip : ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∀ w ∈ Set.Ioc (0 : ℝ) 2,
        |gp z - gp w| ≤ M * |z - w|) :
    ∀ ⦃a h : ℝ⦄, 0 < h → 0 < a → a + h ≤ 2 →
        |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2 := by
  intro a h hh ha hb
  have hIntG : IntervalIntegrable g MeasureTheory.volume a (a + h) :=
    hint_g ha (by linarith) hb
  have hIntChord : IntervalIntegrable (fun x : ℝ => chordI g a h x)
      MeasureTheory.volume a (a + h) := by
    unfold chordI
    exact ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
  have hChordInt : (∫ x in a..(a + h), chordI g a h x) = h * ((g a + g (a + h)) / 2) :=
    integral_chordI g hh.ne'
  have hsubInt : (∫ x in a..(a + h), chordI g a h x - g x)
      = (∫ x in a..(a + h), chordI g a h x) - ∫ x in a..(a + h), g x :=
    intervalIntegral.integral_sub hIntChord hIntG
  have herr_eq : ((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x
      = (1 / h) * ∫ x in a..(a + h), chordI g a h x - g x := by
    rw [hsubInt, hChordInt]; field_simp [hh.ne']
  have hpoint : ∀ x ∈ Set.uIoc a (a + h), ‖chordI g a h x - g x‖ ≤ M * h ^ 2 := by
    intro x hx
    have hxIoc : x ∈ Set.Ioc a (a + h) := by
      simpa [Set.uIoc_of_le (by linarith : a ≤ a + h)] using hx
    have hxIcc : x ∈ Set.Icc a (a + h) := ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    rw [Real.norm_eq_abs]
    exact chordI_error_bound (g := g) (gp := gp) (M := M)
      hM hh ha hb hderiv hint_gp hlip hxIcc
  have hnorm : ‖∫ x in a..(a + h), chordI g a h x - g x‖ ≤ (M * h ^ 2) * |(a + h) - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x|
        = |(1 / h) * ∫ x in a..(a + h), chordI g a h x - g x| := by rw [herr_eq]
    _ = (1 / h) * ‖∫ x in a..(a + h), chordI g a h x - g x‖ := by
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hh), ← Real.norm_eq_abs]
    _ ≤ (1 / h) * ((M * h ^ 2) * |(a + h) - a|) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = M * h ^ 2 := by rw [show (a + h) - a = h by ring, abs_of_pos hh]; field_simp [hh.ne']

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Per-cell trapezoid bound for `log1mexpReg` (HR constant, brick 2)

Combines `LogRegLipschitz` (`log1mexpReg' = boseAntideriv`, 5-Lipschitz on `(0,2]`)
with the open-left per-cell producer `cell_trapezoid_bound_of_lipschitz_deriv_Ioc`:
on every cell `[a,a+h] ⊆ (0,2]`, `|trap avg − integral avg| ≤ 5 h²`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open scoped Interval

noncomputable section

/-- Per-cell trapezoid bound for `log1mexpReg` on cells `[a,a+h]` with `a > 0`. -/
theorem log1mexpReg_cell_trapezoid_bound_pos :
    ∀ ⦃a h : ℝ⦄, 0 < h → 0 < a → a + h ≤ 2 →
      |((log1mexpReg a + log1mexpReg (a + h)) / 2)
          - (1 / h) * ∫ x in a..(a + h), log1mexpReg x| ≤ (5 : ℝ) * h ^ 2 := by
  refine cell_trapezoid_bound_of_lipschitz_deriv_Ioc (g := log1mexpReg)
    (gp := Erdos.boseAntideriv) (M := 5) (by norm_num) ?_ ?_ ?_ ?_
  · intro z hz; exact log1mexpReg_hasDerivAt_pos hz.1
  · intro u v hu huv _hv; exact log1mexpReg_intervalIntegrable_pos hu huv
  · intro u v hu huv _hv; exact boseAntideriv_intervalIntegrable_pos hu huv
  · exact boseAntideriv_lipschitz_Ioc02

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Open-left head trapezoid theorem (HR constant, brick 2)

Peels the first cell `[0,t]` (controlled by `log1mexpReg_tendsto_zero`, avoiding the
derivative at `0`) and applies the open-left per-cell bound only on cells `k ≥ 1`.
Yields the head asymptotic for `log1mexpReg` (ChatGPT R6).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators Interval

noncomputable section

/-- The first-cell trapezoid error. -/
noncomputable def firstCellTrapErr (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((g 0 + g t) / 2) - (1 / t) * ∫ x in (0 : ℝ)..t, g x

/-- `log1mexpReg 0 = 0` (Lean's total `Real.log 0 = 0`). -/
lemma log1mexpReg_zero : log1mexpReg 0 = 0 := by
  simp [log1mexpReg, log1mexp]

/-- If `g → 0` from the right at `0` and `g 0 = 0`, the first-cell error → 0. -/
theorem firstCellTrapErr_tendsto_zero {g : ℝ → ℝ}
    (hg0 : g 0 = 0) (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (firstCellTrapErr g) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  have hpre : {x : ℝ | ‖g x‖ < ε / 4} ∈ 𝓝[>] (0 : ℝ) := by
    have hb : Metric.ball (0 : ℝ) (ε / 4) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε4
    refine Filter.mem_of_superset (hg hb) (fun x hx => ?_)
    rw [Set.mem_preimage, mem_ball_zero_iff] at hx
    exact hx
  rw [Metric.mem_nhdsWithin_iff] at hpre
  rcases hpre with ⟨δ, hδ, hδsub⟩
  have htSmall : Set.Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := by
    have h1 : Set.Iio δ ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
    have h2 : (Set.Iio δ ∩ Set.Ioi (0 : ℝ)) = Set.Ioo 0 δ := by
      ext y; simp [Set.mem_Ioo, and_comm]
    rw [← h2]; exact Filter.inter_mem h1 self_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, htSmall] with t ht htδ
  have htpos : 0 < t := ht
  have htδ' : t < δ := htδ.2
  have hsmall : ∀ x ∈ Set.Ioc (0 : ℝ) t, ‖g x‖ ≤ ε / 4 := by
    intro x hx
    have hxmem : x ∈ Metric.ball (0 : ℝ) δ ∩ Set.Ioi (0 : ℝ) := by
      refine ⟨?_, hx.1⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos hx.1]
      exact lt_of_le_of_lt hx.2 htδ'
    exact le_of_lt (hδsub hxmem)
  have hgt : ‖g t‖ ≤ ε / 4 := hsmall t ⟨htpos, le_rfl⟩
  have hInt : ‖∫ x in (0 : ℝ)..t, g x‖ ≤ (ε / 4) * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro x hx
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) t := by simpa [Set.uIoc_of_le htpos.le] using hx
    exact hsmall x hxIoc
  have havg : ‖(1 / t) * ∫ x in (0 : ℝ)..t, g x‖ ≤ ε / 4 := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr htpos)]
    calc (1 / t) * ‖∫ x in (0 : ℝ)..t, g x‖
          ≤ (1 / t) * ((ε / 4) * |t - 0|) := mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = ε / 4 := by rw [sub_zero, abs_of_pos htpos]; field_simp [htpos.ne']
  have hmain : ‖firstCellTrapErr g t‖ ≤ ε / 2 := by
    unfold firstCellTrapErr
    rw [hg0]
    have hhalf : ‖(0 + g t) / 2‖ ≤ ε / 8 := by
      rw [zero_add, norm_div]
      have h2 : ‖(2 : ℝ)‖ = 2 := by norm_num
      rw [h2]; nlinarith [hgt, norm_nonneg (g t)]
    calc ‖(0 + g t) / 2 - (1 / t) * ∫ x in (0 : ℝ)..t, g x‖
          ≤ ‖(0 + g t) / 2‖ + ‖(1 / t) * ∫ x in (0 : ℝ)..t, g x‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le ((0 + g t) / 2) (-((1 / t) * ∫ x in (0 : ℝ)..t, g x))
      _ ≤ ε / 8 + ε / 4 := add_le_add hhalf havg
      _ ≤ ε / 2 := by linarith
  rw [dist_eq_norm, sub_zero]
  exact lt_of_le_of_lt hmain (by linarith)

/-- First-cell estimate for `log1mexpReg`. -/
theorem log1mexpReg_first_cell_tendsto_zero :
    Tendsto (firstCellTrapErr log1mexpReg) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  firstCellTrapErr_tendsto_zero log1mexpReg_zero log1mexpReg_tendsto_zero

/-- Open-left head theorem (range form): peel cell 0, apply `hcell_pos` on `k ≥ 1`. -/
theorem trapezoid_head_range_tendsto_of_cell_bound_pos
    {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hint : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → b ≤ 2 →
        IntervalIntegrable g MeasureTheory.volume a b)
    (hfirst : Tendsto (firstCellTrapErr g) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hcell_pos : ∀ ⦃a h : ℝ⦄, 0 < h → 0 < a → a + h ≤ 2 →
        |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2) :
    Tendsto
      (fun t : ℝ =>
        (∑ k ∈ Finset.range (trapN t), g (((k + 1 : ℕ) : ℝ) * t))
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), g x)
          - (1 / 2) * (g (trapR t) - g 0))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  have hbound :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ‖(∑ k ∈ Finset.range (trapN t), g (((k + 1 : ℕ) : ℝ) * t))
            - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), g x)
            - (1 / 2) * (g (trapR t) - g 0)‖
          ≤ ‖firstCellTrapErr g t‖ + M * t := by
    filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with t ht ht01
    have htpos : 0 < t := ht
    have ht_le_one : t ≤ 1 := le_of_lt ht01
    set N : ℕ := trapN t with hNdef
    have hNpos : 0 < N := by
      have h1le : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ htpos]; simpa using ht_le_one
      have hfloor : 1 ≤ ⌊1 / t⌋₊ := Nat.le_floor (by exact_mod_cast h1le)
      rw [hNdef, trapN]; exact hfloor
    have hNle : (N : ℝ) ≤ 1 / t := by
      rw [hNdef, trapN]; exact Nat.floor_le (by positivity : 0 ≤ 1 / t)
    have hRt_le_one : (N : ℝ) * t ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right hNle htpos.le
      have hunit : (1 / t) * t = 1 := by rw [one_div]; exact inv_mul_cancel₀ htpos.ne'
      linarith
    have hRt_le_two : (N : ℝ) * t ≤ 2 := by linarith
    have hIntCells : ∀ k ∈ Finset.range N,
        IntervalIntegrable g MeasureTheory.volume ((k : ℝ) * t) (((k + 1 : ℕ) : ℝ) * t) := by
      intro k hk
      have hkleN_real : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      have hright_le_two : (((k + 1 : ℕ) : ℝ) * t) ≤ 2 := by
        have := mul_le_mul_of_nonneg_right hkleN_real htpos.le; linarith
      have hab : (k : ℝ) * t ≤ ((k + 1 : ℕ) : ℝ) * t := by
        push_cast; nlinarith [htpos.le]
      exact hint (by positivity) hab hright_le_two
    have hid := trapezoid_sum_identity_range (g := g) (t := t) (N := N) hIntCells
    let F : ℕ → ℝ := fun k =>
      (((g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
        - (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x)
    have hF0 : F 0 = firstCellTrapErr g t := by unfold F firstCellTrapErr; simp
    have hcellRest : ∀ k ∈ (Finset.range N).erase 0, |F k| ≤ M * t ^ 2 := by
      intro k hk
      have hkrange : k ∈ Finset.range N := Finset.mem_of_mem_erase hk
      have hkpos_nat : 0 < k := Nat.pos_of_ne_zero (Finset.mem_erase.mp hk).1
      have hkpos : 0 < (k : ℝ) * t := by positivity
      have hkleN_real : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hkrange)
      have hright_le_two : (((k + 1 : ℕ) : ℝ) * t) ≤ 2 := by
        have := mul_le_mul_of_nonneg_right hkleN_real htpos.le; linarith
      have haeq : (k : ℝ) * t + t = (((k + 1 : ℕ) : ℝ) * t) := by push_cast; ring
      have hcell := hcell_pos (a := (k : ℝ) * t) (h := t)
        htpos hkpos (by rw [haeq]; exact hright_le_two)
      simpa [F, haeq] using hcell
    rw [trapR, ← hNdef, ← hid, Real.norm_eq_abs]
    have hsplit : (∑ k ∈ Finset.range N, F k)
        = F 0 + ∑ k ∈ (Finset.range N).erase 0, F k := by
      rw [← Finset.add_sum_erase (s := Finset.range N) (a := 0) (f := F)
        (Finset.mem_range.mpr hNpos)]
    rw [show (∑ k ∈ Finset.range N,
        (((g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
          - (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x))
        = ∑ k ∈ Finset.range N, F k from rfl]
    rw [hsplit, hF0]
    calc |firstCellTrapErr g t + ∑ k ∈ (Finset.range N).erase 0, F k|
          ≤ |firstCellTrapErr g t| + |∑ k ∈ (Finset.range N).erase 0, F k| := abs_add_le _ _
      _ ≤ |firstCellTrapErr g t| + ∑ k ∈ (Finset.range N).erase 0, |F k| := by
            linarith [Finset.abs_sum_le_sum_abs F ((Finset.range N).erase 0)]
      _ ≤ |firstCellTrapErr g t| + ∑ _k ∈ (Finset.range N).erase 0, M * t ^ 2 := by
            linarith [Finset.sum_le_sum hcellRest]
      _ = |firstCellTrapErr g t| + ((Finset.range N).erase 0).card * (M * t ^ 2) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ |firstCellTrapErr g t| + (N : ℝ) * (M * t ^ 2) := by
            have hcard : (((Finset.range N).erase 0).card : ℝ) ≤ (N : ℝ) := by
              have h := Finset.card_erase_le (s := Finset.range N) (a := 0)
              rw [Finset.card_range] at h; exact_mod_cast h
            have hnon : 0 ≤ M * t ^ 2 := by positivity
            nlinarith
      _ = |firstCellTrapErr g t| + M * ((N : ℝ) * t ^ 2) := by ring
      _ ≤ |firstCellTrapErr g t| + M * t := by
            have hNt2 : (N : ℝ) * t ^ 2 ≤ t := by nlinarith [hRt_le_one, htpos.le]
            have hmul := mul_le_mul_of_nonneg_left hNt2 hM
            linarith
  have hRHS : Tendsto (fun t : ℝ => ‖firstCellTrapErr g t‖ + M * t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfirstNorm : Tendsto (fun t : ℝ => ‖firstCellTrapErr g t‖)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hfirst
    have hMt : Tendsto (fun t : ℝ => M * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have htend : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using htend.const_mul M
    simpa using hfirstNorm.add hMt
  exact squeeze_zero_norm' hbound hRHS

/-- Open-left head theorem in `Icc 1 (trapN t)` form. -/
theorem trapezoid_head_tendsto_of_cell_bound_pos
    {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hint : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → b ≤ 2 →
        IntervalIntegrable g MeasureTheory.volume a b)
    (hfirst : Tendsto (firstCellTrapErr g) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hcell_pos : ∀ ⦃a h : ℝ⦄, 0 < h → 0 < a → a + h ≤ 2 →
        |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2) :
    Tendsto
      (fun t : ℝ =>
        (∑ k ∈ Finset.Icc 1 (trapN t), g ((k : ℝ) * t))
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), g x)
          - (1 / 2) * (g (trapR t) - g 0))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := trapezoid_head_range_tendsto_of_cell_bound_pos
    (g := g) (M := M) hM hint hfirst hcell_pos
  refine h.congr' ?_
  filter_upwards with t
  rw [sum_Icc_one_eq_sum_range_succ (fun k : ℕ => g ((k : ℝ) * t)) (trapN t)]

/-- The usable head theorem for `log1mexpReg` (conditional on `[0,b]` integrability). -/
theorem log1mexpReg_head_trapezoid_tendsto_zero
    (hint : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → b ≤ 2 →
        IntervalIntegrable log1mexpReg MeasureTheory.volume a b) :
    Tendsto
      (fun t : ℝ =>
        (∑ k ∈ Finset.Icc 1 (trapN t), log1mexpReg ((k : ℝ) * t))
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexpReg x)
          - (1 / 2) * (log1mexpReg (trapR t) - log1mexpReg 0))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  trapezoid_head_tendsto_of_cell_bound_pos (g := log1mexpReg) (M := (5 : ℝ))
    (by norm_num) hint log1mexpReg_first_cell_tendsto_zero log1mexpReg_cell_trapezoid_bound_pos

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Head asymptotic for `log1mexp` (HR constant, brick 2)

Combines the regularized head (`TrapezoidHeadPos`, integrability discharged via
`LogRegIntegrable`) with the singular Stirling head (`StirlingHead`, the `2π`
source), using `log1mexp = log1mexpReg - log` and `∫₀ᴿ log = R log R - R`:

  `headLog1mexp t - (1/t)∫₀ᴿ log1mexp - ½log(t/2π) - ½ log1mexpReg(R) → 0`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators Real
open scoped Topology BigOperators Interval

noncomputable section

/-- `headLog1mexp t = ∑_{k=1}^{N t} log1mexp(k·t)`. -/
noncomputable def headLog1mexp (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (trapN t), log1mexp ((k : ℝ) * t)

/-- The regularized head, integrability discharged via `LogRegIntegrable`. -/
lemma log1mexpReg_head_unconditional :
    Tendsto (fun t : ℝ =>
        (∑ k ∈ Finset.Icc 1 (trapN t), log1mexpReg ((k : ℝ) * t))
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexpReg x)
          - (1 / 2 : ℝ) * (log1mexpReg (trapR t) - log1mexpReg 0))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  log1mexpReg_head_trapezoid_tendsto_zero
    (fun _a _b ha hab hb => log1mexpReg_intervalIntegrable_of_le ha hab hb)

section
end

set_option backward.isDefEq.respectTransparency false in
/-- **Head asymptotic for `log1mexp`** (the `2π` enters here via `singularHead_stirling`). -/
theorem log1mexp_head_asymp :
    Tendsto (fun t : ℝ =>
        headLog1mexp t
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexp x)
          - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))
          - (1 / 2 : ℝ) * log1mexpReg (trapR t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcomb := log1mexpReg_head_unconditional.add singularHead_stirling
  rw [add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have hRle : trapR t ≤ 1 := by
    rw [trapR]
    calc ((trapN t : ℝ)) * t ≤ (1 / t) * t :=
          mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) htpos.le
      _ = 1 := by field_simp
  have hRnn : 0 ≤ trapR t := by rw [trapR]; positivity
  -- (A) sum identity:  Σ log1mexpReg(kt) + singularHead = headLog1mexp
  have hA : (∑ k ∈ Finset.Icc 1 (trapN t), log1mexpReg ((k : ℝ) * t)) + singularHead t
      = headLog1mexp t := by
    unfold singularHead headLog1mexp
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [log1mexpReg, mul_comm t (k : ℝ)]; ring
  -- (B) integral identity:  ∫ log1mexp = ∫ log1mexpReg - ∫ log
  have hII_reg : IntervalIntegrable log1mexpReg MeasureTheory.volume 0 (trapR t) :=
    log1mexpReg_intervalIntegrable_of_le le_rfl hRnn (le_trans hRle (by norm_num))
  have hII_log : IntervalIntegrable Real.log MeasureTheory.volume 0 (trapR t) :=
    intervalIntegral.intervalIntegrable_log'
  have hB : (∫ x in (0 : ℝ)..(trapR t), log1mexp x)
      = (∫ x in (0 : ℝ)..(trapR t), log1mexpReg x) - (∫ x in (0 : ℝ)..(trapR t), Real.log x) := by
    rw [← intervalIntegral.integral_sub hII_reg hII_log]
    apply intervalIntegral.integral_congr
    intro x _hx
    simp only [log1mexpReg]; ring
  -- (C) ∫₀ᴿ log = R log R - R
  have hlogint : (∫ x in (0 : ℝ)..(trapR t), Real.log x)
      = trapR t * Real.log (trapR t) - trapR t := by
    rw [integral_log]; simp
  have hC : log1mexpReg 0 = 0 := by simp [log1mexpReg, log1mexp]
  -- assemble
  unfold singularHeadMain
  rw [hC, hB, hlogint, ← hA]
  field_simp
  ring

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Tail calculus + summability for `log1mexp` (HR constant, brick 2 tail)

Self-contained foundation for the exponential-tail trapezoid (ChatGPT R8):
derivative/second-derivative exp-decay bounds, geometric sum, tail integrability,
sample summability, and the `O(t)` geometric error. The infinite-cell trapezoid
summation + final tail theorem build on these.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open scoped Topology BigOperators Interval

noncomputable section

/-- Derivative of `log1mexp` in tail form: `log1mexp'(x) = -1/(e^x - 1)`. -/
lemma log1mexp_hasDerivAt_tail {x : ℝ} (hx : 0 < x) :
    HasDerivAt log1mexp (-(1 / (Real.exp x - 1))) x := by
  have h := log1mexp_hasDerivAt hx
  convert h using 1
  rw [Real.exp_neg]
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have hden : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hx).ne'
  field_simp

/-- `(-1/(e^x-1))' = e^x/(e^x-1)²`. -/
lemma log1mexpDeriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -(1 / (Real.exp y - 1)))
      (Real.exp x / (Real.exp x - 1) ^ 2) x := by
  have hden_deriv : HasDerivAt (fun y : ℝ => Real.exp y - 1) (Real.exp x) x := by
    simpa using (Real.hasDerivAt_exp x).sub_const 1
  have hden_ne : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hx).ne'
  have hneg := (hden_deriv.inv hden_ne).neg
  simp only [one_div]
  convert hneg using 1
  ring

/-- Second-derivative tail bound: `|e^x/(e^x-1)²| ≤ 4 e^{-x}` for `x ≥ log 2`. -/
lemma log1mexp_second_deriv_tail_bound {x : ℝ} (hx : Real.log 2 ≤ x) :
    |Real.exp x / (Real.exp x - 1) ^ 2| ≤ 4 * Real.exp (-x) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hx
  have he2 : 2 ≤ Real.exp x := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
  have hden_half : Real.exp x / 2 ≤ Real.exp x - 1 := by linarith
  have hden_pos : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hxpos)
  have hden_sq : (Real.exp x / 2) ^ 2 ≤ (Real.exp x - 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hden_half 2
  have hmain : Real.exp x / (Real.exp x - 1) ^ 2 ≤ Real.exp x / ((Real.exp x / 2) ^ 2) :=
    div_le_div₀ (by positivity) le_rfl (by positivity) hden_sq
  have hsimp : Real.exp x / ((Real.exp x / 2) ^ 2) = 4 * Real.exp (-x) := by
    rw [Real.exp_neg]; field_simp [Real.exp_ne_zero x]; ring
  rw [abs_of_pos (by positivity : 0 < Real.exp x / (Real.exp x - 1) ^ 2)]
  exact hmain.trans_eq hsimp

/-- `∑_j e^{-(a+h·j)} = e^{-a}/(1-e^{-h})`. -/
lemma exp_tail_geometric_bound {a h : ℝ} (hh : 0 < h) :
    (∑' j : ℕ, Real.exp (-(a + h * (j : ℝ)))) = Real.exp (-a) / (1 - Real.exp (-h)) := by
  have hr0 : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have hr1 : Real.exp (-h) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hcongr : (fun j : ℕ => Real.exp (-(a + h * (j : ℝ))))
      = fun j : ℕ => Real.exp (-a) * (Real.exp (-h)) ^ j := by
    funext j
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  rw [hcongr, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- For `0 < h ≤ 1`, `1 - e^{-h} ≥ h/2`. -/
lemma one_sub_exp_neg_ge_half {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    h / 2 ≤ 1 - Real.exp (-h) := by
  have hexp_le : Real.exp (-h) ≤ 1 / (1 + h) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp h])
  have h1h : (1 : ℝ) + h ≠ 0 := by positivity
  have hbase : 1 - 1 / (1 + h) = h / (1 + h) := by field_simp; ring
  have hhalf : h / 2 ≤ h / (1 + h) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity : (0 : ℝ) < 1 + h)]; nlinarith
  linarith

/-- `log1mexp` is integrable on a tail `Ioi a` (`a ≥ log 2`). -/
lemma log1mexp_integrableOn_Ioi_tail {a : ℝ} (ha : Real.log 2 ≤ a) :
    IntegrableOn log1mexp (Set.Ioi a) := by
  have hmeas : AEStronglyMeasurable log1mexp (volume.restrict (Set.Ioi a)) := by
    apply Measurable.aestronglyMeasurable
    unfold log1mexp
    exact (Real.measurable_log.comp
      (measurable_const.sub (Real.measurable_exp.comp measurable_neg))).neg
  have hdom : IntegrableOn (fun x : ℝ => 2 * Real.exp (-x)) (Set.Ioi a) := by
    have hbase : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi a) := by
      simpa [one_mul] using exp_neg_integrableOn_Ioi a one_pos
    exact hbase.const_mul 2
  apply Integrable.mono' hdom hmeas
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  rw [Real.norm_eq_abs]
  exact log1mexp_tail_bound (le_trans ha hx.le)

/-- Tail samples are summable. -/
lemma summable_log1mexp_tail_samples {a h : ℝ} (ha : Real.log 2 ≤ a) (hh : 0 < h) :
    Summable (fun j : ℕ => log1mexp (a + h * ((j + 1 : ℕ) : ℝ))) := by
  have hr0 : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have hr1 : Real.exp (-h) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hgeo : Summable (fun j : ℕ => 2 * Real.exp (-(a + h)) * (Real.exp (-h)) ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_norm_bounded hgeo ?_
  intro j
  have hx : Real.log 2 ≤ a + h * ((j + 1 : ℕ) : ℝ) := by
    have hnon : 0 ≤ h * ((j + 1 : ℕ) : ℝ) := by positivity
    linarith
  rw [Real.norm_eq_abs]
  calc |log1mexp (a + h * ((j + 1 : ℕ) : ℝ))|
        ≤ 2 * Real.exp (-(a + h * ((j + 1 : ℕ) : ℝ))) := log1mexp_tail_bound hx
    _ = 2 * Real.exp (-(a + h)) * (Real.exp (-h)) ^ j := by
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring

/-- Tail samples tend to zero. -/
lemma log1mexp_tail_samples_tendsto_zero {a h : ℝ} (ha : Real.log 2 ≤ a) (hh : 0 < h) :
    Tendsto (fun n : ℕ => log1mexp (a + h * (n : ℝ))) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => a + h * (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop a (tendsto_natCast_atTop_atTop.const_mul_atTop hh)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖log1mexp (a + h * (n : ℝ))‖ ≤ 2 * Real.exp (-(a + h * (n : ℝ))) := by
    filter_upwards [eventually_ge_atTop 0] with n _hn
    have hxge : Real.log 2 ≤ a + h * (n : ℝ) := by
      have hnon : 0 ≤ h * (n : ℝ) := by positivity
      linarith
    rw [Real.norm_eq_abs]
    exact log1mexp_tail_bound hxge
  have hzero : Tendsto (fun n : ℕ => 2 * Real.exp (-(a + h * (n : ℝ)))) atTop (𝓝 0) := by
    have hreal : Tendsto (fun x : ℝ => 2 * Real.exp (-x)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2
    exact hreal.comp hx
  exact squeeze_zero_norm' hbound hzero

/-- The geometric tail error bound is `O(t) → 0`. -/
lemma tail_geometric_error_tendsto_zero :
    Tendsto (fun t : ℝ => (4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ‖(4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t)))‖ ≤ 8 * t := by
    filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with t ht ht1
    have htpos : 0 < t := ht
    have htle : t ≤ 1 := le_of_lt ht1
    have hden : t / 2 ≤ 1 - Real.exp (-t) := one_sub_exp_neg_ge_half htpos htle
    have hdenpos : 0 < 1 - Real.exp (-t) := by linarith
    have hexp_le_one : Real.exp (-(trapR t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hRnn : 0 ≤ trapR t := by rw [trapR]; positivity
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t)))
          ≤ 4 * t ^ 2 * (1 / (t / 2)) := by gcongr
      _ = 8 * t := by field_simp; ring
  have ht : Tendsto (fun t : ℝ => 8 * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using h0.const_mul (8 : ℝ)
  exact squeeze_zero_norm' hbound ht

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# `log1mexp` integrability and integral split on `(0,∞)` (HR constant, brick 2 assembly)

`log1mexp` is integrable on `Ioi 0` (singularity at `0` dissolved via
`log1mexp = log1mexpReg - log` on `(0,1]`, exponential tail on `(1,∞)`), and the
integral splits at any `R ≥ 0`: `∫₀ᴿ + ∫_{Ioi R} = ∫_{Ioi 0}`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory
open scoped Topology BigOperators Interval

noncomputable section

/-- `log1mexp` is integrable on `(0,∞)`. -/
lemma log1mexp_integrableOn_Ioi_zero :
    IntegrableOn log1mexp (Set.Ioi (0 : ℝ)) := by
  have hlog2_le_one : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  -- regularized part on `(0,1]`
  have hregII : IntervalIntegrable log1mexpReg MeasureTheory.volume (0 : ℝ) 1 :=
    log1mexpReg_intervalIntegrable_of_le
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
  have hreg : IntegrableOn log1mexpReg (Set.Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hregII
  -- `Real.log` interval-integrable through `0`
  have hlogII : IntervalIntegrable Real.log MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_log'
  have hlog : IntegrableOn Real.log (Set.Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hlogII
  have hnear_sub : IntegrableOn (fun x : ℝ => log1mexpReg x - Real.log x) (Set.Ioc (0 : ℝ) 1) :=
    hreg.sub hlog
  have hnear : IntegrableOn log1mexp (Set.Ioc (0 : ℝ) 1) := by
    refine hnear_sub.congr_fun ?_ measurableSet_Ioc
    intro x hx
    simp [log1mexpReg]
  -- exponential tail on `(1,∞)`
  have htail : IntegrableOn log1mexp (Set.Ioi (1 : ℝ)) :=
    log1mexp_integrableOn_Ioi_tail hlog2_le_one
  have hsplit : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)
  rw [← hsplit]
  exact hnear.union htail

/-- Split the integral over `(0,∞)` at `R ≥ 0`:
`∫₀ᴿ log1mexp + ∫_{Ioi R} log1mexp = ∫_{Ioi 0} log1mexp`. -/
lemma log1mexp_integral_split {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in (0 : ℝ)..R, log1mexp x) + (∫ x in Set.Ioi R, log1mexp x)
      = ∫ x in Set.Ioi (0 : ℝ), log1mexp x := by
  have hglob : IntegrableOn log1mexp (Set.Ioi (0 : ℝ)) := log1mexp_integrableOn_Ioi_zero
  have hIoc : IntegrableOn log1mexp (Set.Ioc (0 : ℝ) R) :=
    hglob.mono_set (by intro x hx; exact hx.1)
  have hIoi : IntegrableOn log1mexp (Set.Ioi R) :=
    hglob.mono_set (by intro x hx; exact lt_of_le_of_lt hR hx)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) R) (Set.Ioi R) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxIoc hxIoi
    have h1 := hxIoc.2
    have h2 := hxIoi
    simp only [Set.mem_Ioi] at h2
    linarith
  have hsplit : Set.Ioc (0 : ℝ) R ∪ Set.Ioi R = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hR
  have hunion := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIoc hIoi
  rw [hsplit] at hunion
  rw [intervalIntegral.integral_of_le hR]
  exact hunion.symm

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Local-domain per-cell trapezoid bound (HR constant, brick 2 tail)

Per-cell trapezoid error `≤ L·h²` from a Lipschitz derivative on the cell `[a,a+h]`
itself (local-domain version of `TrapezoidCellIoc`, chord-interpolation proof).
Then the concrete `log1mexp` tail cell bound `≤ 4 e^{-a} h²` (ChatGPT R8 route).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology MeasureTheory Real
open scoped Topology Interval

noncomputable section

/-- Chord through `(a,g a)`, `(a+h,g(a+h))`. -/
private noncomputable def chordT (g : ℝ → ℝ) (a h x : ℝ) : ℝ :=
  ((g (a + h) - g a) / h) * x + (((a + h) * g a - a * g (a + h)) / h)

private lemma chordT_eq_endpoint (g : ℝ → ℝ) {a h x : ℝ} (hh : h ≠ 0) :
    chordT g a h x = ((a + h - x) / h) * g a + ((x - a) / h) * g (a + h) := by
  unfold chordT; field_simp [hh]; ring

private lemma integral_chordT (g : ℝ → ℝ) {a h : ℝ} (hh : h ≠ 0) :
    (∫ x in a..(a + h), chordT g a h x) = h * ((g a + g (a + h)) / 2) := by
  unfold chordT
  set A : ℝ := (g (a + h) - g a) / h with hA
  set B : ℝ := ((a + h) * g a - a * g (a + h)) / h with hB
  have hInt1 : IntervalIntegrable (fun x : ℝ => A * x) MeasureTheory.volume a (a + h) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable (fun _x : ℝ => B) MeasureTheory.volume a (a + h) :=
    continuous_const.intervalIntegrable _ _
  change (∫ x in a..(a + h), A * x + B) = h * ((g a + g (a + h)) / 2)
  rw [intervalIntegral.integral_add hInt1 hInt2, intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const]
  rw [hA, hB]; simp only [smul_eq_mul]; field_simp [hh]; ring

private lemma first_order_error_local
    {g gp : ℝ → ℝ} {L a h x y : ℝ} (hL : 0 ≤ L)
    (hxI : x ∈ Set.Icc a (a + h)) (hyI : y ∈ Set.Icc a (a + h))
    (hderiv : ∀ z ∈ Set.Icc a (a + h), HasDerivAt g (gp z) z)
    (hint_gp : IntervalIntegrable gp MeasureTheory.volume a (a + h))
    (hlip : ∀ z ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc a (a + h), |gp z - gp w| ≤ L * |z - w|) :
    |g y - g x - (y - x) * gp x| ≤ L * (y - x) ^ 2 := by
  have hsub : Set.uIcc x y ⊆ Set.Icc a (a + h) := Set.uIcc_subset_Icc hxI hyI
  have hIntGp : IntervalIntegrable gp MeasureTheory.volume x y :=
    hint_gp.mono_set (by rw [Set.uIcc_of_le (le_trans hxI.1 hxI.2)]; exact hsub)
  have hIntConst : IntervalIntegrable (fun _z : ℝ => gp x) MeasureTheory.volume x y :=
    continuous_const.intervalIntegrable _ _
  have hIntDiff : IntervalIntegrable (fun z : ℝ => gp z - gp x) MeasureTheory.volume x y :=
    hIntGp.sub hIntConst
  have hderivF : ∀ z ∈ Set.uIcc x y,
      HasDerivAt (fun z : ℝ => g z - z * gp x) (gp z - gp x) z := by
    intro z hz
    have hg := hderiv z (hsub hz)
    have hlin : HasDerivAt (fun z : ℝ => z * gp x) (gp x) z := by
      simpa using (hasDerivAt_id z).mul_const (gp x)
    exact hg.sub hlin
  have hFTC : (∫ z in x..y, gp z - gp x) = (g y - y * gp x) - (g x - x * gp x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderivF hIntDiff
  have herr_eq : g y - g x - (y - x) * gp x = ∫ z in x..y, gp z - gp x := by rw [hFTC]; ring
  have hnorm : ‖∫ z in x..y, gp z - gp x‖ ≤ (L * |y - x|) * |y - x| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro z hz
    have hzmem : z ∈ Set.uIcc x y := Set.Ioc_subset_Icc_self hz
    have hzI : z ∈ Set.Icc a (a + h) := hsub hzmem
    have hzx : |z - x| ≤ |y - x| := by
      rcases le_total x y with hle | hle
      · rw [Set.uIoc_of_le hle] at hz
        rw [abs_of_nonneg (by linarith [hz.1] : (0:ℝ) ≤ z - x),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]; linarith [hz.2]
      · rw [Set.uIoc_comm, Set.uIoc_of_le hle] at hz
        rw [abs_of_nonpos (by linarith [hz.2] : z - x ≤ 0),
          abs_of_nonpos (by linarith : y - x ≤ 0)]; linarith [hz.1]
    rw [Real.norm_eq_abs]
    calc |gp z - gp x| ≤ L * |z - x| := hlip z hzI x hxI
      _ ≤ L * |y - x| := mul_le_mul_of_nonneg_left hzx hL
  calc |g y - g x - (y - x) * gp x| = ‖∫ z in x..y, gp z - gp x‖ := by
        rw [herr_eq, Real.norm_eq_abs]
    _ ≤ (L * |y - x|) * |y - x| := hnorm
    _ = L * (y - x) ^ 2 := by rw [mul_assoc, abs_mul_abs_self]; ring

private lemma chordT_error_bound
    {g gp : ℝ → ℝ} {L a h x : ℝ} (hL : 0 ≤ L) (hh : 0 < h)
    (hderiv : ∀ z ∈ Set.Icc a (a + h), HasDerivAt g (gp z) z)
    (hint_gp : IntervalIntegrable gp MeasureTheory.volume a (a + h))
    (hlip : ∀ z ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc a (a + h), |gp z - gp w| ≤ L * |z - w|)
    (hx : x ∈ Set.Icc a (a + h)) :
    |chordT g a h x - g x| ≤ L * h ^ 2 := by
  have hxa : a ≤ x := hx.1
  have hxb : x ≤ a + h := hx.2
  have haI : a ∈ Set.Icc a (a + h) := ⟨le_rfl, by linarith⟩
  have habI : a + h ∈ Set.Icc a (a + h) := ⟨by linarith, le_rfl⟩
  have e1 : |g x - g a - (x - a) * gp x| ≤ L * (x - a) ^ 2 := by
    have hfo := first_order_error_local (g := g) (gp := gp) (L := L) (x := x) (y := a)
      hL hx haI hderiv hint_gp hlip
    rw [show g x - g a - (x - a) * gp x = -(g a - g x - (a - x) * gp x) by ring, abs_neg,
      show (x - a) ^ 2 = (a - x) ^ 2 by ring]
    exact hfo
  have e2 : |g (a + h) - g x - (a + h - x) * gp x| ≤ L * (a + h - x) ^ 2 :=
    first_order_error_local (g := g) (gp := gp) (L := L) (x := x) (y := a + h)
      hL hx habI hderiv hint_gp hlip
  have hα : 0 ≤ x - a := sub_nonneg.mpr hxa
  have hβ : 0 ≤ a + h - x := sub_nonneg.mpr hxb
  have hαh : 0 ≤ (x - a) / h := div_nonneg hα hh.le
  have hβh : 0 ≤ (a + h - x) / h := div_nonneg hβ hh.le
  have herr : g x - chordT g a h x =
      ((a + h - x) / h) * (g x - g a - (x - a) * gp x)
        - ((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x) := by
    rw [chordT_eq_endpoint g hh.ne']; field_simp [hh.ne']; ring
  have hterm1 : |((a + h - x) / h) * (g x - g a - (x - a) * gp x)|
        ≤ ((a + h - x) / h) * (L * (x - a) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hβh]; exact mul_le_mul_of_nonneg_left e1 hβh
  have hterm2 : |((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)|
        ≤ ((x - a) / h) * (L * (a + h - x) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hαh]; exact mul_le_mul_of_nonneg_left e2 hαh
  have hmain : |g x - chordT g a h x| ≤ L * (x - a) * (a + h - x) := by
    rw [herr]
    calc |((a + h - x) / h) * (g x - g a - (x - a) * gp x)
            - ((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)|
          ≤ |((a + h - x) / h) * (g x - g a - (x - a) * gp x)|
            + |((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)| := abs_sub _ _
      _ ≤ ((a + h - x) / h) * (L * (x - a) ^ 2)
            + ((x - a) / h) * (L * (a + h - x) ^ 2) := add_le_add hterm1 hterm2
      _ = L * (x - a) * (a + h - x) := by field_simp [hh.ne']; ring
  rw [abs_sub_comm]
  calc |g x - chordT g a h x| ≤ L * (x - a) * (a + h - x) := hmain
    _ ≤ L * h ^ 2 := by
        have hαle : x - a ≤ h := by linarith
        have hβle : a + h - x ≤ h := by linarith
        nlinarith [hL, hα, hβ, hαle, hβle]

/-- Per-cell trapezoid bound from a Lipschitz derivative on the cell `[a,a+h]`. -/
theorem cell_trapezoid_bound_of_local_lipschitz_deriv
    {g gp : ℝ → ℝ} {L a h : ℝ} (hL : 0 ≤ L) (hh : 0 < h)
    (hderiv : ∀ x ∈ Set.Icc a (a + h), HasDerivAt g (gp x) x)
    (hint_g : IntervalIntegrable g MeasureTheory.volume a (a + h))
    (hint_gp : IntervalIntegrable gp MeasureTheory.volume a (a + h))
    (hlip : ∀ z ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc a (a + h), |gp z - gp w| ≤ L * |z - w|) :
    |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ L * h ^ 2 := by
  have hChordInt : (∫ x in a..(a + h), chordT g a h x) = h * ((g a + g (a + h)) / 2) :=
    integral_chordT g hh.ne'
  have hIntChord : IntervalIntegrable (fun x : ℝ => chordT g a h x)
      MeasureTheory.volume a (a + h) := by
    unfold chordT
    exact ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
  have hsubInt : (∫ x in a..(a + h), chordT g a h x - g x)
      = (∫ x in a..(a + h), chordT g a h x) - ∫ x in a..(a + h), g x :=
    intervalIntegral.integral_sub hIntChord hint_g
  have herr_eq : ((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x
      = (1 / h) * ∫ x in a..(a + h), chordT g a h x - g x := by
    rw [hsubInt, hChordInt]; field_simp [hh.ne']
  have hpoint : ∀ x ∈ Set.uIoc a (a + h), ‖chordT g a h x - g x‖ ≤ L * h ^ 2 := by
    intro x hx
    have hxIoc : x ∈ Set.Ioc a (a + h) := by
      simpa [Set.uIoc_of_le (by linarith : a ≤ a + h)] using hx
    have hxIcc : x ∈ Set.Icc a (a + h) := ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    rw [Real.norm_eq_abs]
    exact chordT_error_bound (g := g) (gp := gp) (L := L) hL hh hderiv hint_gp hlip hxIcc
  have hnorm : ‖∫ x in a..(a + h), chordT g a h x - g x‖ ≤ (L * h ^ 2) * |(a + h) - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x|
        = |(1 / h) * ∫ x in a..(a + h), chordT g a h x - g x| := by rw [herr_eq]
    _ = (1 / h) * ‖∫ x in a..(a + h), chordT g a h x - g x‖ := by
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hh), ← Real.norm_eq_abs]
    _ ≤ (1 / h) * ((L * h ^ 2) * |(a + h) - a|) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = L * h ^ 2 := by rw [show (a + h) - a = h by ring, abs_of_pos hh]; field_simp [hh.ne']

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# `log1mexp` per-cell tail bound (HR constant, brick 2 tail)

`log1mexp'(x) = -1/(e^x-1)` is `4e^{-a}`-Lipschitz on a tail cell `[a,a+h]` (a ≥ log 2),
via FTC on its derivative `e^x/(e^x-1)²` (bounded `≤ 4e^{-x}`). Hence the per-cell
trapezoid error is `≤ 4 e^{-a} h²` (apply `cell_trapezoid_bound_of_local_lipschitz_deriv`).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology MeasureTheory Real
open scoped Topology Interval

noncomputable section

/-- `log1mexp'` is `4e^{-a}`-Lipschitz on a tail cell `[a,a+h]` (`a ≥ log 2`). -/
lemma log1mexp_deriv_lipschitz_tail_cell {a h : ℝ} (ha : Real.log 2 ≤ a) :
    ∀ z ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc a (a + h),
      |-(1 / (Real.exp z - 1)) - -(1 / (Real.exp w - 1))| ≤ (4 * Real.exp (-a)) * |z - w| := by
  intro z hz w hw
  have hge : ∀ x ∈ Set.uIcc z w, a ≤ x := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with h | h
    · exact le_trans hz.1 h.1
    · exact le_trans hw.1 h.1
  have hxpos : ∀ x ∈ Set.uIcc z w, 0 < x := fun x hx =>
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (le_trans ha (hge x hx))
  have hderiv : ∀ x ∈ Set.uIcc z w,
      HasDerivAt (fun y : ℝ => -(1 / (Real.exp y - 1))) (Real.exp x / (Real.exp x - 1) ^ 2) x :=
    fun x hx => log1mexpDeriv_hasDerivAt (hxpos x hx)
  have hcont : ContinuousOn (fun x : ℝ => Real.exp x / (Real.exp x - 1) ^ 2) (Set.uIcc z w) := by
    intro x hx
    have hden : (Real.exp x - 1) ^ 2 ≠ 0 := by
      have : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (hxpos x hx)); positivity
    exact ((Real.continuous_exp.continuousAt).div
      (((Real.continuous_exp.sub continuous_const).pow 2).continuousAt) hden).continuousWithinAt
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp x / (Real.exp x - 1) ^ 2)
      MeasureTheory.volume z w := hcont.intervalIntegrable
  have hFTC : (∫ x in z..w, Real.exp x / (Real.exp x - 1) ^ 2)
      = (-(1 / (Real.exp w - 1))) - (-(1 / (Real.exp z - 1))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hpoint : ∀ x ∈ Set.uIoc z w, ‖Real.exp x / (Real.exp x - 1) ^ 2‖ ≤ 4 * Real.exp (-a) := by
    intro x hx
    have hxge : a ≤ x := hge x (Set.Ioc_subset_Icc_self hx)
    rw [Real.norm_eq_abs]
    calc |Real.exp x / (Real.exp x - 1) ^ 2| ≤ 4 * Real.exp (-x) :=
          log1mexp_second_deriv_tail_bound (le_trans ha hxge)
      _ ≤ 4 * Real.exp (-a) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  have hnorm : ‖∫ x in z..w, Real.exp x / (Real.exp x - 1) ^ 2‖ ≤ (4 * Real.exp (-a)) * |w - z| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc |-(1 / (Real.exp z - 1)) - -(1 / (Real.exp w - 1))|
        = ‖∫ x in z..w, Real.exp x / (Real.exp x - 1) ^ 2‖ := by
          rw [hFTC, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ (4 * Real.exp (-a)) * |w - z| := hnorm
    _ = (4 * Real.exp (-a)) * |z - w| := by rw [abs_sub_comm]

/-- Per-cell tail trapezoid bound for `log1mexp`: `≤ 4 e^{-a} h²`. -/
lemma log1mexp_tail_cell_bound {a h : ℝ} (hh : 0 < h) (ha : Real.log 2 ≤ a) :
    |((log1mexp a + log1mexp (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), log1mexp x|
      ≤ (4 * Real.exp (-a)) * h ^ 2 := by
  have hderiv : ∀ x ∈ Set.Icc a (a + h), HasDerivAt log1mexp (-(1 / (Real.exp x - 1))) x :=
    fun x hx => log1mexp_hasDerivAt_tail
      (lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (le_trans ha hx.1))
  have hint_g : IntervalIntegrable log1mexp MeasureTheory.volume a (a + h) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith : a ≤ a + h)] at hx
    exact (log1mexp_hasDerivAt_tail
      (lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (le_trans ha hx.1))).continuousAt.continuousWithinAt
  have hint_gp : IntervalIntegrable (fun x : ℝ => -(1 / (Real.exp x - 1)))
      MeasureTheory.volume a (a + h) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith : a ≤ a + h)] at hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (le_trans ha hx.1)
    have hden : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hxpos).ne'
    exact ((continuousAt_const.div
      (Real.continuous_exp.continuousAt.sub continuousAt_const) hden).neg).continuousWithinAt
  exact cell_trapezoid_bound_of_local_lipschitz_deriv (by positivity) hh hderiv hint_g hint_gp
    (log1mexp_deriv_lipschitz_tail_cell ha)

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Infinite-cell tail trapezoid summation (HR constant, brick 2 tail)

The exponential-tail trapezoid theorem (ChatGPT R8): from per-cell errors decaying
like `C e^{-(a+jh)} h²`, the right-endpoint tail expression is `O(h) → 0`. Uses
disjoint shifted cells covering `Ioi a` (`hasSum_integral_iUnion`) + telescoping.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real Function
open scoped Topology BigOperators Interval

noncomputable section

/-- One tail trapezoid cell error on `[a+jh, a+(j+1)h]`. -/
noncomputable def tailTrapErr (f : ℝ → ℝ) (a h : ℝ) (j : ℕ) : ℝ :=
  ((f (a + h * (j : ℝ)) + f (a + h * ((j + 1 : ℕ) : ℝ))) / 2)
    - (1 / h) * ∫ x in (a + h * (j : ℝ))..(a + h * ((j + 1 : ℕ) : ℝ)), f x

/-- Shifted tail cells. -/
def tailCell (a h : ℝ) (j : ℕ) : Set ℝ :=
  Set.Ioc (a + h * (j : ℝ)) (a + h * ((j + 1 : ℕ) : ℝ))

/-- Pairwise disjoint shifted tail cells. -/
private lemma pairwise_disjoint_tailCell {a h : ℝ} (hh : 0 ≤ h) :
    Pairwise (Disjoint on tailCell a h) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : i + 1 ≤ j := by omega
    have hreal : (((i + 1 : ℕ) : ℝ) ≤ (j : ℝ)) := by exact_mod_cast hnat
    have hle : a + h * ((i + 1 : ℕ) : ℝ) ≤ a + h * (j : ℝ) := by
      have := mul_le_mul_of_nonneg_left hreal hh; linarith
    linarith [hxi.2, hxj.1, hle]
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : j + 1 ≤ i := by omega
    have hreal : (((j + 1 : ℕ) : ℝ) ≤ (i : ℝ)) := by exact_mod_cast hnat
    have hle : a + h * ((j + 1 : ℕ) : ℝ) ≤ a + h * (i : ℝ) := by
      have := mul_le_mul_of_nonneg_left hreal hh; linarith
    linarith [hxj.2, hxi.1, hle]

/-- The shifted tail cells cover `Ioi a`. -/
private lemma iUnion_tailCell_eq_Ioi {a h : ℝ} (hh : 0 < h) :
    (⋃ j : ℕ, tailCell a h j) = Set.Ioi a := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    exact lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hj.1
  · intro hx
    let y : ℝ := (x - a) / h
    have hy_pos : 0 < y := by dsimp [y]; exact div_pos (sub_pos.mpr hx) hh
    let n : ℕ := Nat.ceil y
    have hn_pos : 0 < n := (Nat.ceil_pos (a := y)).mpr hy_pos
    let j : ℕ := n - 1
    have hj_succ : j + 1 = n := by dsimp [j]; omega
    have hj_lt_y : (j : ℝ) < y := by
      have hlt_nat : j < Nat.ceil y := by dsimp [j, n]; omega
      exact (Nat.lt_ceil (a := y) (n := j)).mp hlt_nat
    have hy_le_succ : y ≤ (((j + 1 : ℕ) : ℝ)) := by
      have hy_le_n : y ≤ (n : ℝ) := by
        have hnn : Nat.ceil y ≤ n := by simp [n]
        exact (Nat.ceil_le (a := y) (n := n)).mp hnn
      simpa [hj_succ] using hy_le_n
    have hmul : a + h * y = x := by dsimp [y]; field_simp [hh.ne']; ring
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [tailCell]
    constructor
    · calc a + h * (j : ℝ) < a + h * y := by linarith [mul_lt_mul_of_pos_left hj_lt_y hh]
        _ = x := hmul
    · calc x = a + h * y := hmul.symm
        _ ≤ a + h * ((j + 1 : ℕ) : ℝ) := by linarith [mul_le_mul_of_nonneg_left hy_le_succ hh.le]

theorem tail_trapezoid_bound_of_exp_cell_errors
    {f : ℝ → ℝ} {a h C : ℝ}
    (hh : 0 < h) (hC : 0 ≤ C)
    (hfint : IntegrableOn f (Set.Ioi a))
    (hsamp : Summable (fun j : ℕ => f (a + h * ((j + 1 : ℕ) : ℝ))))
    (hzero : Tendsto (fun n : ℕ => f (a + h * (n : ℝ))) atTop (𝓝 0))
    (hcell :
      ∀ j : ℕ,
        |tailTrapErr f a h j| ≤ C * Real.exp (-(a + h * (j : ℝ))) * h ^ 2) :
    |(∑' j : ℕ, f (a + h * ((j + 1 : ℕ) : ℝ)))
        - (1 / h) * (∫ x in Set.Ioi a, f x)
        + (1 / 2) * f a|
      ≤ C * h ^ 2 * (Real.exp (-a) / (1 - Real.exp (-h))) := by
  classical

  -- Cell integral decomposition of `∫_{a}^{∞}`.
  let B : ℕ → ℝ := fun j =>
    ∫ x in tailCell a h j, f x
  have hUnion : (⋃ j : ℕ, tailCell a h j) = Set.Ioi a :=
    iUnion_tailCell_eq_Ioi (a := a) (h := h) hh
  have hpair : Pairwise (Disjoint on tailCell a h) :=
    pairwise_disjoint_tailCell (a := a) (h := h) hh.le
  have hmeas : ∀ j : ℕ, MeasurableSet (tailCell a h j) := by
    intro j
    simp [tailCell]
  have hB_has :
      HasSum B (∫ x in Set.Ioi a, f x) := by
    have h_int_union : IntegrableOn f (⋃ j : ℕ, tailCell a h j) := by
      simpa [hUnion] using hfint
    simpa [B, hUnion] using
      (hasSum_integral_iUnion (μ := volume) (f := f) hmeas hpair h_int_union)

  -- Absolute summability of cell errors from the exponential majorant.
  have hgeom_summ :
      Summable (fun j : ℕ => C * Real.exp (-(a + h * (j : ℝ))) * h ^ 2) := by
    have hr0 : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
    have hr1 : Real.exp (-h) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have hgeo : Summable (fun j : ℕ => (Real.exp (-h)) ^ j) :=
      summable_geometric_of_lt_one hr0 hr1
    refine hgeo.mul_left (C * Real.exp (-a) * h ^ 2) |>.congr ?_
    intro j
    rw [← Real.exp_nat_mul,
      show C * Real.exp (-a) * h ^ 2 * Real.exp ((j : ℝ) * -h)
        = C * h ^ 2 * (Real.exp (-a) * Real.exp ((j : ℝ) * -h)) by ring,
      ← Real.exp_add, show -a + (j : ℝ) * -h = -(a + h * (j : ℝ)) by ring]
    ring

  have herr_abs_summ :
      Summable (fun j : ℕ => |tailTrapErr f a h j|) :=
    Summable.of_nonneg_of_le
      (fun j => abs_nonneg _)
      hcell
      hgeom_summ
  have herr_summ : Summable (tailTrapErr f a h) :=
    Summable.of_abs herr_abs_summ

  -- The finite partial identity:
  -- `∑_{j<N} err_j = ∑_{j<N} f(a+(j+1)h) - (1/h)∑_{j<N}B_j
  --                  + 1/2 f(a) - 1/2 f(a+Nh)`.
  have hpartial :
      ∀ N : ℕ,
        (∑ j ∈ Finset.range N, tailTrapErr f a h j)
          =
        (∑ j ∈ Finset.range N, f (a + h * ((j + 1 : ℕ) : ℝ)))
          - (1 / h) * (∑ j ∈ Finset.range N, B j)
          + (1 / 2) * f a
          - (1 / 2) * f (a + h * (N : ℝ)) := by
    intro N
    have hBeq : ∀ j : ℕ,
        (∫ x in (a + h * (j : ℝ))..(a + h * ((j + 1 : ℕ) : ℝ)), f x) = B j := by
      intro j
      show (∫ x in (a + h * (j : ℝ))..(a + h * ((j + 1 : ℕ) : ℝ)), f x)
        = ∫ x in tailCell a h j, f x
      rw [tailCell, intervalIntegral.integral_of_le (by push_cast; nlinarith [hh.le])]
    unfold tailTrapErr
    simp_rw [hBeq]
    rw [Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    have htrap :
        (∑ j ∈ Finset.range N,
          (f (a + h * (j : ℝ)) + f (a + h * ((j + 1 : ℕ) : ℝ))) / 2)
        =
        (∑ j ∈ Finset.range N, f (a + h * ((j + 1 : ℕ) : ℝ)))
          + (1 / 2) * f a
          - (1 / 2) * f (a + h * (N : ℝ)) := by
      -- telescoping endpoint identity
      have hshift :=
        sum_range_succ_sub_sum_range
          (fun n : ℕ => f (a + h * (n : ℝ))) N
      have hsplit :
          (∑ j ∈ Finset.range N,
            (f (a + h * (j : ℝ)) + f (a + h * ((j + 1 : ℕ) : ℝ))) / 2)
          =
          ((∑ j ∈ Finset.range N, f (a + h * (j : ℝ)))
            + (∑ j ∈ Finset.range N, f (a + h * ((j + 1 : ℕ) : ℝ)))) / 2 := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_div]
      rw [hsplit]
      simp only [Nat.cast_zero, mul_zero, add_zero] at hshift
      linarith
    rw [htrap]
    ring

  -- Pass finite partial identity to the limit.
  have hleft_lim :
      Tendsto
        (fun N : ℕ => ∑ j ∈ Finset.range N, tailTrapErr f a h j)
        atTop (𝓝 (∑' j : ℕ, tailTrapErr f a h j)) :=
    herr_summ.hasSum.tendsto_sum_nat

  have hsamp_lim :
      Tendsto
        (fun N : ℕ => ∑ j ∈ Finset.range N, f (a + h * ((j + 1 : ℕ) : ℝ)))
        atTop (𝓝 (∑' j : ℕ, f (a + h * ((j + 1 : ℕ) : ℝ)))) :=
    hsamp.hasSum.tendsto_sum_nat

  have hB_lim :
      Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, B j)
        atTop (𝓝 (∫ x in Set.Ioi a, f x)) :=
    hB_has.tendsto_sum_nat

  have hend_lim :
      Tendsto (fun N : ℕ => f (a + h * (N : ℝ))) atTop (𝓝 0) :=
    hzero

  have hright_lim :
      Tendsto
        (fun N : ℕ =>
          (∑ j ∈ Finset.range N, f (a + h * ((j + 1 : ℕ) : ℝ)))
            - (1 / h) * (∑ j ∈ Finset.range N, B j)
            + (1 / 2) * f a
            - (1 / 2) * f (a + h * (N : ℝ)))
        atTop
        (𝓝 ((∑' j : ℕ, f (a + h * ((j + 1 : ℕ) : ℝ)))
          - (1 / h) * (∫ x in Set.Ioi a, f x)
          + (1 / 2) * f a
          - (1 / 2) * 0)) := by
    have key := Filter.Tendsto.sub
      ((hsamp_lim.sub (hB_lim.const_mul (1 / h))).add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2) * f a) atTop (𝓝 ((1 / 2) * f a))))
      (hend_lim.const_mul (1 / 2))
    convert key using 2

  have htsum_eq :
      (∑' j : ℕ, tailTrapErr f a h j)
        =
      (∑' j : ℕ, f (a + h * ((j + 1 : ℕ) : ℝ)))
          - (1 / h) * (∫ x in Set.Ioi a, f x)
          + (1 / 2) * f a := by
    have heq_lim := tendsto_nhds_unique hleft_lim
      (hright_lim.congr' (Eventually.of_forall (fun N => (hpartial N).symm)))
    simpa using heq_lim

  -- Bound the tsum of errors by the geometric majorant.
  have hsum_abs :
      |∑' j : ℕ, tailTrapErr f a h j|
        ≤ ∑' j : ℕ, |tailTrapErr f a h j| := by
    have hh2 : Summable (fun j : ℕ => ‖tailTrapErr f a h j‖) := by
      simpa [Real.norm_eq_abs] using herr_abs_summ
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hh2

  have hgeom_bound :
      (∑' j : ℕ, |tailTrapErr f a h j|)
        ≤ ∑' j : ℕ, C * Real.exp (-(a + h * (j : ℝ))) * h ^ 2 := by
    exact Summable.tsum_le_tsum hcell herr_abs_summ hgeom_summ

  have hgeom_eval :
      (∑' j : ℕ, C * Real.exp (-(a + h * (j : ℝ))) * h ^ 2)
        =
      C * h ^ 2 * (Real.exp (-a) / (1 - Real.exp (-h))) := by
    rw [show (fun j : ℕ => C * Real.exp (-(a + h * (j : ℝ))) * h ^ 2)
        = fun j : ℕ => (C * h ^ 2) * Real.exp (-(a + h * (j : ℝ))) by
      funext j; ring]
    rw [tsum_mul_left, exp_tail_geometric_bound (a := a) (h := h) hh]

  rw [← htsum_eq]
  exact hsum_abs.trans (hgeom_bound.trans_eq hgeom_eval)

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Concrete `log1mexp` tail trapezoid theorem (HR constant, brick 2 tail)

Instantiates the generic infinite-cell tail summation
`tail_trapezoid_bound_of_exp_cell_errors` at `a = trapR t`, `h = t`, `C = 4`,
`f = log1mexp`, and squeezes the geometric `O(t)` majorant to zero:

`∑_{j≥0} log1mexp((N+1+j)t) − (1/t)∫_{R}^{∞} log1mexp + ½·log1mexp(R) → 0`
as `t → 0⁺` (where `N = trapN t`, `R = trapR t = N·t`).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open scoped Topology BigOperators Interval

noncomputable section

/-- Near `0⁺`, the head cutoff `R(t) = N(t)·t` is eventually `≥ log 2`
(since `R → 1 > log 2`). -/
lemma eventually_log_two_le_trapR :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), Real.log 2 ≤ trapR t := by
  have h2e : (2 : ℝ) < Real.exp 1 := lt_of_lt_of_le (by norm_num) Real.exp_one_gt_d9.le
  have hlt : Real.log 2 < 1 := by
    calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2e
      _ = 1 := Real.log_exp 1
  exact trapR_tendsto_one.eventually (eventually_ge_nhds hlt)

/--
**Tail trapezoid theorem for `log1mexp`.**

The right-endpoint infinite tail after the head cutoff vanishes as `t → 0⁺`:
`∑_{j≥0} log1mexp((N+1+j)t) − (1/t)∫_{R}^{∞} log1mexp + ½·log1mexp(R) → 0`.
-/
theorem log1mexp_tail_trapezoid :
    Tendsto
      (fun t : ℝ =>
        (∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          - (1 / t) * (∫ x in Set.Ioi (trapR t), log1mexp x)
          + (1 / 2 : ℝ) * log1mexp (trapR t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbound :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ‖(∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          - (1 / t) * (∫ x in Set.Ioi (trapR t), log1mexp x)
          + (1 / 2 : ℝ) * log1mexp (trapR t)‖
        ≤ (4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t))) := by
    filter_upwards [self_mem_nhdsWithin, eventually_log_two_le_trapR]
      with t ht hRlog2
    have htpos : 0 < t := ht
    have hcell : ∀ j : ℕ,
        |tailTrapErr log1mexp (trapR t) t j|
          ≤ 4 * Real.exp (-(trapR t + t * (j : ℝ))) * t ^ 2 := by
      intro j
      have haj : Real.log 2 ≤ trapR t + t * (j : ℝ) := by
        have hnon : 0 ≤ t * (j : ℝ) := by positivity
        linarith
      have hcellj := log1mexp_tail_cell_bound (a := trapR t + t * (j : ℝ))
        (h := t) htpos haj
      -- the j-th cell starts at `R + t·j`; its `(j+1)` upper endpoint is `R + t·j + t`
      have hcast : trapR t + t * ((j + 1 : ℕ) : ℝ) = trapR t + t * (j : ℝ) + t := by
        push_cast; ring
      unfold tailTrapErr
      rw [hcast]
      exact hcellj
    have htail :=
      tail_trapezoid_bound_of_exp_cell_errors
        (f := log1mexp) (a := trapR t) (h := t) (C := (4 : ℝ))
        htpos (by norm_num)
        (log1mexp_integrableOn_Ioi_tail hRlog2)
        (summable_log1mexp_tail_samples hRlog2 htpos)
        (log1mexp_tail_samples_tendsto_zero hRlog2 htpos)
        hcell
    have hsum_eq :
        (∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          =
        ∑' j : ℕ, log1mexp (trapR t + t * ((j + 1 : ℕ) : ℝ)) := by
      apply tsum_congr
      intro j
      rw [trapR]
      congr 1
      push_cast
      ring
    rw [Real.norm_eq_abs, hsum_eq]
    exact htail
  exact squeeze_zero_norm' hbound tail_geometric_error_tendsto_zero

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Second-order Laplace asymptotic for the partition generating function (HR brick 2)

Assembles the head asymptotic (`log1mexp_head_asymp`) and the tail asymptotic
(`log1mexp_tail_trapezoid`) into the Meinardus second-order law

`log P(e^{-t}) = (1/t)·I + ½·log(2π/t) + o(1)`,  `I = ∫₀^∞ -log(1-e^{-x}) dx`,

i.e. `log P(e^{-t}) − (1/t)·I − ½·log(t/2π) → 0` as `t → 0⁺`, where
`P(e^{-t}) = PartLaplace t = ∑ p(n) e^{-tn}` and `log1mexp x = -log(1-e^{-x})`.

The key splice: `log P = headLog1mexp + tail` (finite head + infinite tail of the
Euler-log series), `∫₀ᴿ + ∫_R^∞ = ∫₀^∞`, and the head/tail boundary regularizers
cancel up to `−½ log R` with `R = trapR t → 1`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open scoped Topology BigOperators Interval

noncomputable section

/-- `log P(e^{-t})` splits as the finite head sum plus the infinite tail samples. -/
lemma log_partLaplace_eq_head_add_tail {t : ℝ} (ht : 0 < t) :
    headLog1mexp t + (∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
      = Real.log (PartLaplace t) := by
  set N := trapN t with hN
  -- (1) `log P = ∑' n:ℕ, log1mexp (t·(n+1))`
  have hL2 : Real.log (PartLaplace t) = ∑' n : ℕ, log1mexp (t * ((n + 1 : ℕ) : ℝ)) := by
    have h1 : Real.log (PartLaplace t) = ∑' k : ℕ+, log1mexp (t * (k : ℝ)) := by
      rw [log_partLaplace_eq ht]
      apply tsum_congr; intro k
      rw [log1mexp]
    rw [h1, tsum_pnat_eq_tsum_succ (f := fun m : ℕ => log1mexp (t * (m : ℝ)))]
  -- (2) summability of the full series
  have hsumm : Summable (fun n : ℕ => log1mexp (t * ((n + 1 : ℕ) : ℝ))) := by
    obtain ⟨M, hM⟩ : ∃ M : ℕ, Real.log 2 ≤ (M : ℝ) * t := by
      obtain ⟨M, hMge⟩ := exists_nat_ge (Real.log 2 / t)
      exact ⟨M, (div_le_iff₀ ht).mp hMge⟩
    have htailM : Summable (fun n : ℕ => log1mexp ((M : ℝ) * t + t * ((n + 1 : ℕ) : ℝ))) :=
      summable_log1mexp_tail_samples hM ht
    have hcongr :
        (fun n : ℕ => log1mexp (t * (((n + M) + 1 : ℕ) : ℝ)))
          = (fun n : ℕ => log1mexp ((M : ℝ) * t + t * ((n + 1 : ℕ) : ℝ))) := by
      funext n; congr 1; push_cast; ring
    have hshift : Summable (fun n : ℕ => log1mexp (t * (((n + M) + 1 : ℕ) : ℝ))) := by
      rw [hcongr]; exact htailM
    exact (summable_nat_add_iff (f := fun m : ℕ => log1mexp (t * ((m + 1 : ℕ) : ℝ))) M).mp hshift
  -- (3) finite/infinite split of the tsum
  have hsplit := hsumm.sum_add_tsum_nat_add N
  -- (4) head reindex: `∑_{i<N} log1mexp(t·(i+1)) = headLog1mexp t`
  have hhead :
      (∑ i ∈ Finset.range N, log1mexp (t * ((i + 1 : ℕ) : ℝ))) = headLog1mexp t := by
    unfold headLog1mexp
    have hIccIco : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
      ext x; simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
    rw [← hN, hIccIco, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
    congr 2
    push_cast; ring
  -- (5) tail reindex: `∑' i, log1mexp(t·(i+N+1)) = tail samples`
  have htail :
      (∑' i : ℕ, log1mexp (t * (((i + N) + 1 : ℕ) : ℝ)))
        = ∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t) := by
    apply tsum_congr; intro i
    rw [mul_comm, ← hN]
    congr 2
    push_cast; ring
  rw [hhead, htail] at hsplit
  rw [hsplit, ← hL2]

/-- **Second-order Laplace asymptotic, with-`I` form.**
`log P(e^{-t}) − (1/t)·∫₀^∞ log1mexp − ½·log(t/2π) → 0` as `t → 0⁺`. -/
theorem log_partLaplace_second_order_with_I :
    Tendsto
      (fun t : ℝ =>
        Real.log (PartLaplace t)
          - (1 / t) * (∫ x in Set.Ioi (0 : ℝ), log1mexp x)
          - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- head + tail asymptotics, summed
  have hsum :
      Tendsto
        (fun t : ℝ =>
          (headLog1mexp t
            - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexp x)
            - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))
            - (1 / 2 : ℝ) * log1mexpReg (trapR t))
          + ((∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
            - (1 / t) * (∫ x in Set.Ioi (trapR t), log1mexp x)
            + (1 / 2 : ℝ) * log1mexp (trapR t)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [add_zero] using log1mexp_head_asymp.add log1mexp_tail_trapezoid
  -- this sum equals `G(t) − ½ log(trapR t)` for `t > 0`
  have heq :
      (fun t : ℝ =>
        (headLog1mexp t
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexp x)
          - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))
          - (1 / 2 : ℝ) * log1mexpReg (trapR t))
        + ((∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          - (1 / t) * (∫ x in Set.Ioi (trapR t), log1mexp x)
          + (1 / 2 : ℝ) * log1mexp (trapR t)))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ =>
        (Real.log (PartLaplace t)
          - (1 / t) * (∫ x in Set.Ioi (0 : ℝ), log1mexp x)
          - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
        - (1 / 2 : ℝ) * Real.log (trapR t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have hR0 : (0 : ℝ) ≤ trapR t := by rw [trapR]; positivity
    have hstart := log_partLaplace_eq_head_add_tail htpos
    have hint :
        (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexp x)
          + (1 / t) * (∫ x in Set.Ioi (trapR t), log1mexp x)
          = (1 / t) * (∫ x in Set.Ioi (0 : ℝ), log1mexp x) := by
      rw [← mul_add, log1mexp_integral_split hR0]
    simp only [log1mexpReg]
    linarith [hstart, hint]
  have hGwith :
      Tendsto
        (fun t : ℝ =>
          (Real.log (PartLaplace t)
            - (1 / t) * (∫ x in Set.Ioi (0 : ℝ), log1mexp x)
            - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
          - (1 / 2 : ℝ) * Real.log (trapR t))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := hsum.congr' heq
  -- `½ log(trapR t) → 0` since `trapR → 1`
  have hlogR : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.log (trapR t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => Real.log (trapR t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp trapR_tendsto_one
      simpa using this
    simpa using hc.const_mul (1 / 2 : ℝ)
  -- add back the boundary term
  have hadd := hGwith.add hlogR
  simp only [add_zero] at hadd
  refine hadd.congr' (Eventually.of_forall fun t => ?_)
  ring

/-- The Laplace integral constant equals the first-order constant: `∫₀^∞ log1mexp = A`.
Proof: `t·log P → I` (from the second-order law) and `t·log P → A`
(`partition_laplace_log_asymptotic`); limits are unique. -/
theorem log1mexp_integral_eq_A :
    (∫ x in Set.Ioi (0 : ℝ), log1mexp x) = A := by
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  -- `t·φ(t) → 0` where `φ` is the second-order remainder
  have htphi := ht0.mul log_partLaplace_second_order_with_I
  rw [mul_zero] at htphi
  -- `t·½log(t/2π) → 0`
  have htlog :
      Tendsto (fun t : ℝ => t * ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hxlogx : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) (by norm_num : (0 : ℝ) < 1)
      simp only [Real.rpow_one] at h
      exact h.congr (fun x => mul_comm _ _)
    have hconst : Tendsto (fun t : ℝ => t * Real.log (2 * Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ht0.mul_const (Real.log (2 * Real.pi))
    have hcombo :
        Tendsto (fun t : ℝ => (1 / 2 : ℝ) * (t * Real.log t - t * Real.log (2 * Real.pi)))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (hxlogx.sub hconst).const_mul (1 / 2 : ℝ)
    refine hcombo.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    rw [Real.log_div (ne_of_gt htpos) (by positivity)]
    ring
  -- assemble `t·log P → I`
  have hL :
      Tendsto (fun t : ℝ => t * Real.log (PartLaplace t)) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ x in Set.Ioi (0 : ℝ), log1mexp x)) := by
    have hcomb :=
      (htphi.add (tendsto_const_nhds
        (x := (∫ x in Set.Ioi (0 : ℝ), log1mexp x)))).add htlog
    simp only [zero_add, add_zero] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := ne_of_gt ht
    field_simp
    ring
  exact tendsto_nhds_unique hL partition_laplace_log_asymptotic

/-- **Second-order Laplace asymptotic (Meinardus main term), final form.**
`log P(e^{-t}) − A/t − ½·log(t/2π) → 0` as `t → 0⁺`, with `A = π²/6`. -/
theorem log_partLaplace_second_order :
    Tendsto
      (fun t : ℝ =>
        Real.log (PartLaplace t)
          - (1 / t) * A
          - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := log_partLaplace_second_order_with_I
  rw [log1mexp_integral_eq_A] at h
  exact h

end
end AnalyticCombinatorics.Ch8.Partitions
end

/-!
# Hardy–Ramanujan constant: brick 5 algebra (HR constant avenue d)

The pure-`√` constant identity underlying `a = 1/(4√3)`:
`(4√π / C)·√(2π) = 4√3`, where `C = π√(2/3)` and `C² = 4A = 2π²/3`.

This is the arithmetic core that bricks 2–4 feed into: with `K = 4√π/C` the saddle
prefactor and `√(2π)` the Meinardus prefactor, the limit constant is
`a = 1/(K·√(2π)) = 1/(4√3)`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos

noncomputable section

/-- `C² = 2π²/3`. -/
lemma C_sq_eq : C ^ 2 = 2 * Real.pi ^ 2 / 3 := by
  rw [C_sq_eq_four_mul_A, Partitions.A]
  ring

/-- The saddle/Meinardus prefactor product collapses to `4√3`:
`(4√π / C)·√(2π) = 4√3`. -/
lemma saddle_meinardus_const_identity :
    (4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi) = 4 * Real.sqrt 3 := by
  have hCpos : 0 < C := C_pos
  have hL : 0 ≤ (4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi) :=
    mul_nonneg (div_nonneg (by positivity) hCpos.le) (Real.sqrt_nonneg _)
  have hR : 0 ≤ 4 * Real.sqrt 3 := by positivity
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have key :
      ((4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi)) ^ 2 = (4 * Real.sqrt 3) ^ 2 := by
    rw [show ((4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi)) ^ 2
          = 16 * (Real.sqrt Real.pi ^ 2) * (Real.sqrt (2 * Real.pi) ^ 2) / C ^ 2 by
        field_simp; ring,
      Real.sq_sqrt (le_of_lt Real.pi_pos),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi), C_sq_eq,
      show (4 * Real.sqrt 3) ^ 2 = 16 * (Real.sqrt 3 ^ 2) by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    field_simp
  calc (4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi)
      = Real.sqrt (((4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi)) ^ 2) :=
        (Real.sqrt_sq hL).symm
    _ = Real.sqrt ((4 * Real.sqrt 3) ^ 2) := by rw [key]
    _ = 4 * Real.sqrt 3 := Real.sqrt_sq hR

end
end AnalyticCombinatorics.Ch8.Partitions

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions
open Filter Topology Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
theorem solution
    {a : ℝ} (ha : 0 < a)
    (hB3 :
      Tendsto
        (fun t : ℝ => Real.log (PartLaplace t) - Real.log a - Real.log (modelSaddle t))
        (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hB4 :
      Tendsto
        (fun t : ℝ =>
          Real.log (modelSaddle t) - A / t - (1 / 2 : ℝ) * Real.log t
            - Real.log (4 * Real.sqrt Real.pi / C))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    a = 1 / (4 * Real.sqrt 3) := by
  have hCpos : 0 < C := C_pos
  have hKpos : 0 < 4 * Real.sqrt Real.pi / C := div_pos (by positivity) hCpos
  -- combine brick 3 + brick 4 - brick 2 → a constant tending to 0
  have hdiff := (hB3.add hB4).sub log_partLaplace_second_order
  simp only [add_zero, sub_zero] at hdiff
  have hconst :
      Tendsto
        (fun _ : ℝ =>
          -Real.log a - Real.log (4 * Real.sqrt Real.pi / C)
            - (1 / 2 : ℝ) * Real.log (2 * Real.pi))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hdiff.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    rw [Real.log_div (ne_of_gt htpos) (by positivity)]
    ring
  have hzero :
      -Real.log a - Real.log (4 * Real.sqrt Real.pi / C)
        - (1 / 2 : ℝ) * Real.log (2 * Real.pi) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  -- solve `log a = log (1/(4√3))`, conclude by injectivity
  have h2pi : (1 / 2 : ℝ) * Real.log (2 * Real.pi) = Real.log (Real.sqrt (2 * Real.pi)) := by
    rw [Real.log_sqrt (by positivity)]; ring
  have hlog_a : Real.log a = Real.log (1 / (4 * Real.sqrt 3)) := by
    have hstep : Real.log a
        = -(Real.log (4 * Real.sqrt Real.pi / C) + Real.log (Real.sqrt (2 * Real.pi))) := by
      rw [← h2pi]; linarith [hzero]
    rw [hstep, ← Real.log_mul (ne_of_gt hKpos)
        (ne_of_gt (Real.sqrt_pos.mpr (by positivity))), saddle_meinardus_const_identity,
      ← Real.log_inv, one_div]
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha)
    (Set.mem_Ioi.mpr (by positivity)) hlog_a
