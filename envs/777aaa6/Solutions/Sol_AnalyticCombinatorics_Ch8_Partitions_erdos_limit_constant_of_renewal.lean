-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.erdos_limit_constant_of_renewal
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:41:48.076267+00:00
-- url     : https://prove2.me/submissions/d5bfe09d-c0d2-4579-8a75-3fb5b015a5dc

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_EulerProduct
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ModelAssembly
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_LaplaceAsymptotic
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosConstant
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_Model_erdos_kernel_window
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_kernelMass_sub_one_rate
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_erdos_limit_constant_of_asymptotics
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

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

end AnalyticCombinatorics.Ch8.Partitions
end

section
namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

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

lemma partsLE_eq_part_of_le {K n : ℕ} (h : n ≤ K) :
    (partsLE K n : ℝ) = part n := by
  dsimp [partsLE, part]
  exact_mod_cast Fintype.card_congr (boundedPartitionTopEquiv K n h)

end AnalyticCombinatorics.Ch8.Partitions
end

section
namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology Asymptotics

-- The final transfer combines real logarithm/square-root limits with field
-- simplification; this keeps those terminal proofs within the local file.
set_option maxHeartbeats 400000

theorem part_zero : part 0 = 1 := by
  simp [part]

end AnalyticCombinatorics.Ch8.Partitions
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

open scoped BigOperators

lemma sigmaR_eq_sum_divisors (m : ℕ) :
    sigmaR m = ∑ d ∈ m.divisors, (d : ℝ) := by
  rw [sigmaR, ArithmeticFunction.sigma_one_apply]
  norm_num

lemma part_eq_weightFiberCard_of_le {K n : ℕ} (h : n ≤ K) :
    part n = (weightFiberCard K n : ℝ) := by
  rw [← partsLE_eq_part_of_le (K := K) (n := n) h]
  exact_mod_cast (partsLE_eq_weightFiberCard K n)

lemma weight_update_add {K : ℕ} (i : Fin K) (k : ℕ) (q : Fin K → ℕ) :
    multiplicityWeight K (Function.update q i (q i + k)) =
      multiplicityWeight K q + (i.1 + 1) * k := by
  classical
  unfold multiplicityWeight
  have hi : i ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ i
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin K => (j.1 + 1) * Function.update q i (q i + k) j) hi]
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin K => (j.1 + 1) * q j) hi]
  have htail :
      (∑ x ∈ Finset.univ.erase i,
          (x.1 + 1) * Function.update q i (q i + k) x) =
        ∑ x ∈ Finset.univ.erase i, (x.1 + 1) * q x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
    simp [hxi]
  rw [htail]
  rw [Function.update_self, Nat.mul_add]
  omega

lemma weight_update_sub {K : ℕ} (i : Fin K) {k : ℕ} (q : Fin K → ℕ) (hk : k ≤ q i) :
    multiplicityWeight K (Function.update q i (q i - k)) + (i.1 + 1) * k =
      multiplicityWeight K q := by
  classical
  unfold multiplicityWeight
  have hi : i ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ i
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin K => (j.1 + 1) * Function.update q i (q i - k) j) hi]
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j : Fin K => (j.1 + 1) * q j) hi]
  have htail :
      (∑ x ∈ Finset.univ.erase i,
          (x.1 + 1) * Function.update q i (q i - k) x) =
        ∑ x ∈ Finset.univ.erase i, (x.1 + 1) * q x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
    simp [hxi]
  rw [htail]
  rw [Function.update_self]
  have hmain :
      (i.1 + 1) * (q i - k) + (i.1 + 1) * k = (i.1 + 1) * q i := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hk]
  omega

noncomputable def addCoordinateFiberEquiv {K t : ℕ} (i : Fin K) (k : ℕ)
    (hkv : (i.1 + 1) * k ≤ t) :
    {q : Fin K → ℕ // multiplicityWeight K q = t - (i.1 + 1) * k} ≃
      {q : {q : Fin K → ℕ // multiplicityWeight K q = t} // k ≤ q.1 i} where
  toFun q := by
    refine ⟨⟨Function.update q.1 i (q.1 i + k), ?_⟩, ?_⟩
    · rw [weight_update_add, q.2]
      omega
    · simp
  invFun q := by
    refine ⟨Function.update q.1.1 i (q.1.1 i - k), ?_⟩
    have hsub := weight_update_sub i q.1.1 q.2
    rw [q.1.2] at hsub
    omega
  left_inv := by
    intro q
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst hji
      simp
    · have hij : i ≠ j := fun h => hji h.symm
      simp [hji]
  right_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst hji
      simp [Nat.sub_add_cancel q.2]
    · have hij : i ≠ j := fun h => hji h.symm
      simp [hji]

lemma fiber_coord_le_div {K t : ℕ} (i : Fin K)
    (q : {q : Fin K → ℕ // multiplicityWeight K q = t}) :
    q.1 i ≤ t / (i.1 + 1) := by
  have hterm : (i.1 + 1) * q.1 i ≤ multiplicityWeight K q.1 := by
    unfold multiplicityWeight
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin K => (j.1 + 1) * q.1 j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [q.2] at hterm
  exact (Nat.le_div_iff_mul_le (Nat.succ_pos i.1)).2 (by
    simpa [Nat.mul_comm] using hterm)

lemma sum_nat_eq_sum_card_ge {α : Type*} [Fintype α] (f : α → ℕ) (B : ℕ)
    (hB : ∀ a, f a ≤ B) :
    (∑ a : α, f a) =
      ∑ k ∈ Finset.Icc 1 B, Fintype.card {a : α // k ≤ f a} := by
  classical
  calc
    (∑ a : α, f a)
        = ∑ a : α, ∑ k ∈ Finset.Icc 1 B, if k ≤ f a then 1 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          have hfilter :
              (Finset.Icc 1 B).filter (fun k => k ≤ f a) = Finset.Icc 1 (f a) := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_Icc]
            have hBa := hB a
            omega
          have hsum :
              (∑ k ∈ Finset.Icc 1 B, if k ≤ f a then 1 else 0)
                = ((Finset.Icc 1 B).filter (fun k => k ≤ f a)).card := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          rw [hsum, hfilter]
          simp
    _ = ∑ k ∈ Finset.Icc 1 B, ∑ a : α, if k ≤ f a then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.Icc 1 B, Fintype.card {a : α // k ≤ f a} := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          rw [Fintype.card_subtype]
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]

lemma fiber_coord_sum_eq (K t : ℕ) (i : Fin K) :
    letI := weightFiberFintype K t
    (∑ q : {q : Fin K → ℕ // multiplicityWeight K q = t}, q.1 i) =
      ∑ k ∈ Finset.Icc 1 (t / (i.1 + 1)),
        weightFiberCard K (t - (i.1 + 1) * k) := by
  classical
  letI := weightFiberFintype K t
  rw [sum_nat_eq_sum_card_ge
    (f := fun q : {q : Fin K → ℕ // multiplicityWeight K q = t} => q.1 i)
    (B := t / (i.1 + 1)) (fun q => fiber_coord_le_div i q)]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_le : k ≤ t / (i.1 + 1) := (Finset.mem_Icc.mp hk).2
  have hkv : (i.1 + 1) * k ≤ t := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (Nat.succ_pos i.1)).1 hk_le
  letI := weightFiberFintype K (t - (i.1 + 1) * k)
  change
      Fintype.card {q : {q : Fin K → ℕ // multiplicityWeight K q = t} // k ≤ q.1 i} =
        Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = t - (i.1 + 1) * k}
  exact (Fintype.card_congr (addCoordinateFiberEquiv i k hkv)).symm

lemma weightFiber_double_recurrence (n : ℕ) :
    n * weightFiberCard n n =
      ∑ i : Fin n, (i.1 + 1) *
        ∑ k ∈ Finset.Icc 1 (n / (i.1 + 1)),
          weightFiberCard n (n - (i.1 + 1) * k) := by
  classical
  letI := weightFiberFintype n n
  calc
    n * weightFiberCard n n
        = ∑ q : {q : Fin n → ℕ // multiplicityWeight n q = n}, n := by
          simp [weightFiberCard, Finset.sum_const, mul_comm]
    _ = ∑ q : {q : Fin n → ℕ // multiplicityWeight n q = n}, multiplicityWeight n q.1 := by
          refine Finset.sum_congr rfl ?_
          intro q _hq
          exact q.2.symm
    _ = ∑ q : {q : Fin n → ℕ // multiplicityWeight n q = n},
          ∑ i : Fin n, (i.1 + 1) * q.1 i := by
          rfl
    _ = ∑ i : Fin n,
          ∑ q : {q : Fin n → ℕ // multiplicityWeight n q = n}, (i.1 + 1) * q.1 i := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin n, (i.1 + 1) *
          ∑ q : {q : Fin n → ℕ // multiplicityWeight n q = n}, q.1 i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ i : Fin n, (i.1 + 1) *
        ∑ k ∈ Finset.Icc 1 (n / (i.1 + 1)),
          weightFiberCard n (n - (i.1 + 1) * k) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [fiber_coord_sum_eq n n i]

lemma divisor_reindex_sum (n : ℕ) (F : ℕ → ℕ) :
    (∑ v ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 (n / v), v * F (v * k)) =
      ∑ m ∈ Finset.Icc 1 n, (∑ d ∈ m.divisors, d) * F m := by
  classical
  let left : Finset (Sigma fun _ : ℕ => ℕ) :=
    (Finset.Icc 1 n).sigma (fun v => Finset.Icc 1 (n / v))
  let right : Finset (Sigma fun _ : ℕ => ℕ) :=
    (Finset.Icc 1 n).sigma (fun m => m.divisors)
  have hbij :
      (∑ x ∈ left, x.1 * F (x.1 * x.2)) =
        ∑ y ∈ right, y.2 * F y.1 := by
    refine Finset.sum_bij
      (fun x _hx => (⟨x.1 * x.2, x.1⟩ : Sigma fun _ : ℕ => ℕ)) ?_ ?_ ?_ ?_
    · intro x hx
      dsimp [left, right] at hx ⊢
      rw [Finset.mem_sigma] at hx ⊢
      rcases hx with ⟨hv, hk⟩
      rw [Finset.mem_Icc] at hv hk ⊢
      constructor
      · constructor
        · exact Nat.mul_pos hv.1 hk.1
        · have hmul := (Nat.le_div_iff_mul_le hv.1).1 hk.2
          simpa [Nat.mul_comm] using hmul
      · exact Nat.mem_divisors.mpr
          ⟨Nat.dvd_mul_right x.1 x.2,
            Nat.mul_ne_zero (Nat.ne_of_gt hv.1) (Nat.ne_of_gt hk.1)⟩
    · intro x hx y hy hxy
      dsimp [left] at hx hy
      rw [Finset.mem_sigma] at hx hy
      rcases hx with ⟨hvx, hkx⟩
      rcases hy with ⟨hvy, hky⟩
      rw [Finset.mem_Icc] at hvx hkx hvy hky
      cases x with
      | mk vx kx =>
      cases y with
      | mk vy ky =>
      simp at hxy
      rcases hxy with ⟨hmul, hv⟩
      subst hv
      have hk : kx = ky := Nat.eq_of_mul_eq_mul_left hvx.1 hmul
      subst hk
      rfl
    · intro y hy
      dsimp [right] at hy
      rw [Finset.mem_sigma] at hy
      rcases hy with ⟨hm, hd⟩
      rw [Finset.mem_Icc] at hm
      have hdvd : y.2 ∣ y.1 := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < y.2 := Nat.pos_of_mem_divisors hd
      have hyle : y.2 ≤ y.1 := Nat.le_of_dvd hm.1 hdvd
      refine ⟨(⟨y.2, y.1 / y.2⟩ : Sigma fun _ : ℕ => ℕ), ?_, ?_⟩
      · dsimp [left]
        rw [Finset.mem_sigma]
        constructor
        · rw [Finset.mem_Icc]
          exact ⟨hdpos, hyle.trans hm.2⟩
        · rw [Finset.mem_Icc]
          constructor
          · exact Nat.div_pos hyle hdpos
          · exact Nat.div_le_div_right hm.2
      · ext <;> simp [Nat.mul_div_cancel' hdvd]
    · intro x hx
      rfl
  calc
    (∑ v ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 (n / v), v * F (v * k))
        = ∑ x ∈ left, x.1 * F (x.1 * x.2) := by
          dsimp [left]
          rw [Finset.sum_sigma']
    _ = ∑ y ∈ right, y.2 * F y.1 := hbij
    _ = ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ m.divisors, d * F m := by
          dsimp [right]
          rw [Finset.sum_sigma']
    _ = ∑ m ∈ Finset.Icc 1 n, (∑ d ∈ m.divisors, d) * F m := by
          refine Finset.sum_congr rfl ?_
          intro m _hm
          rw [Finset.sum_mul]

lemma weightFiber_divisor_recurrence (n : ℕ) :
    n * weightFiberCard n n =
      ∑ m ∈ Finset.Icc 1 n,
        (∑ d ∈ m.divisors, d) * weightFiberCard n (n - m) := by
  rw [weightFiber_double_recurrence]
  calc
    (∑ i : Fin n, (i.1 + 1) *
        ∑ k ∈ Finset.Icc 1 (n / (i.1 + 1)),
          weightFiberCard n (n - (i.1 + 1) * k))
        = ∑ v ∈ Finset.Icc 1 n, v *
            ∑ k ∈ Finset.Icc 1 (n / v), weightFiberCard n (n - v * k) := by
          exact sum_fin_succ_eq_Icc n
            (fun v => v * ∑ k ∈ Finset.Icc 1 (n / v), weightFiberCard n (n - v * k))
    _ = ∑ v ∈ Finset.Icc 1 n,
          ∑ k ∈ Finset.Icc 1 (n / v), v * weightFiberCard n (n - v * k) := by
          refine Finset.sum_congr rfl ?_
          intro v _hv
          rw [Finset.mul_sum]
    _ = ∑ m ∈ Finset.Icc 1 n,
          (∑ d ∈ m.divisors, d) * weightFiberCard n (n - m) := by
          exact divisor_reindex_sum n (fun m => weightFiberCard n (n - m))

theorem partition_sigma_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * part n =
      ∑ m ∈ Finset.Icc 1 n, sigmaR m * part (n - m) := by
  have hnat := weightFiber_divisor_recurrence n
  have hrealCast :
      ((n * weightFiberCard n n : ℕ) : ℝ) =
        ∑ m ∈ Finset.Icc 1 n,
          (∑ d ∈ m.divisors, (d : ℝ)) * (weightFiberCard n (n - m) : ℝ) := by
    simpa using congrArg (fun a : ℕ => (a : ℝ)) hnat
  have hreal :
      (n : ℝ) * (weightFiberCard n n : ℝ) =
        ∑ m ∈ Finset.Icc 1 n,
          (∑ d ∈ m.divisors, (d : ℝ)) * (weightFiberCard n (n - m) : ℝ) := by
    simpa [Nat.cast_mul] using hrealCast
  calc
    (n : ℝ) * part n
        = (n : ℝ) * (weightFiberCard n n : ℝ) := by
          rw [part_eq_weightFiberCard_of_le (K := n) (n := n) (by
            have _ : 1 ≤ n := hn
            exact le_rfl)]
    _ = ∑ m ∈ Finset.Icc 1 n,
          (∑ d ∈ m.divisors, (d : ℝ)) * (weightFiberCard n (n - m) : ℝ) := hreal
    _ = ∑ m ∈ Finset.Icc 1 n, sigmaR m * part (n - m) := by
          refine Finset.sum_congr rfl ?_
          intro m _hm
          rw [sigmaR_eq_sum_divisors]
          rw [part_eq_weightFiberCard_of_le (K := n) (n := n - m) (Nat.sub_le n m)]

end AnalyticCombinatorics.Ch8.Partitions.Sigma
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

lemma sigmaR_le_square {n : ℕ} (hn : 1 ≤ n) :
    Sigma.sigmaR n ≤ (n : ℝ) ^ 2 := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hmem.2)
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hmem.2) hmem.1
    exact Finset.mem_Icc.mpr ⟨hdpos, hdle⟩
  have hcard_nat : n.divisors.card ≤ n := by
    calc
      n.divisors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
      _ = n := by
        simp
  have hsum_le :
      (∑ d ∈ n.divisors, (d : ℝ)) ≤ ∑ _d ∈ n.divisors, (n : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hmem.2) hmem.1
  calc
    (∑ d ∈ n.divisors, (d : ℝ))
        ≤ ∑ _d ∈ n.divisors, (n : ℝ) := hsum_le
    _ = (n.divisors.card : ℝ) * (n : ℝ) := by
          simp [nsmul_eq_mul, mul_comm]
    _ ≤ (n : ℝ) ^ 2 := by
          have hcard : (n.divisors.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard_nat
          have hn0 : 0 ≤ (n : ℝ) := by positivity
          nlinarith

lemma erdosWeight_nonneg_of_mem {n m : ℕ} (hm : m ∈ Finset.Icc 1 (n - 1)) :
    0 ≤ erdosWeight n m := by
  have hmI := Finset.mem_Icc.mp hm
  exact erdosWeight_nonneg_of_lt (n := n) (m := m) (by omega)

theorem u_recurrence (n : ℕ) (hn : 2 ≤ n) :
    u n =
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) +
        boundaryTerm n := by
  classical
  have hn1 : 1 ≤ n := hn.trans' (by norm_num)
  have hrec := Sigma.partition_sigma_recurrence n hn1
  have hsplit :
      (∑ m ∈ Finset.Icc 1 n, Sigma.sigmaR m * Partitions.part (n - m)) =
        (∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m)) +
          Sigma.sigmaR n * Partitions.part 0 := by
    have htop :
        (∑ m ∈ Finset.Icc 1 ((n - 1) + 1),
            Sigma.sigmaR m * Partitions.part (((n - 1) + 1) - m)) =
          (∑ m ∈ Finset.Icc 1 (n - 1),
              Sigma.sigmaR m * Partitions.part (((n - 1) + 1) - m)) +
            Sigma.sigmaR ((n - 1) + 1) *
              Partitions.part (((n - 1) + 1) - ((n - 1) + 1)) := by
      exact Finset.sum_Icc_succ_top
        (a := 1) (b := n - 1)
        (by omega)
        (fun m => Sigma.sigmaR m * Partitions.part (((n - 1) + 1) - m))
    have hnsub : (n - 1) + 1 = n := by omega
    simpa [hnsub] using htop
  have hmain :
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) =
        (∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m) *
              Real.exp (-C * Real.sqrt (n : ℝ))) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmI := Finset.mem_Icc.mp hm
    have hmle : m ≤ n - 1 := hmI.2
    have hmn_pos_nat : 0 < n - m := by omega
    have hmn_pos : 0 < ((n - m : ℕ) : ℝ) := by exact_mod_cast hmn_pos_nat
    have hmn_ne : ((n - m : ℕ) : ℝ) ≠ 0 := hmn_pos.ne'
    have hsqrt_add :
        -C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) +
            (-C * Real.sqrt ((n - m : ℕ) : ℝ)) =
          -C * Real.sqrt (n : ℝ) := by
      ring
    calc
      erdosWeight n m * u (n - m)
          =
            (Sigma.sigmaR m / ((n - m : ℕ) : ℝ) *
                Real.exp (-C *
                  (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))) *
              (((n - m : ℕ) : ℝ) * Partitions.part (n - m) *
                Real.exp (-C * Real.sqrt ((n - m : ℕ) : ℝ))) := by
                  rfl
      _ =
            Sigma.sigmaR m * Partitions.part (n - m) *
              (Real.exp (-C *
                  (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) *
                Real.exp (-C * Real.sqrt ((n - m : ℕ) : ℝ))) := by
                  field_simp [hmn_ne]
      _ =
            Sigma.sigmaR m * Partitions.part (n - m) *
              Real.exp (-C * Real.sqrt (n : ℝ)) := by
                  rw [← Real.exp_add, hsqrt_add]
  calc
    u n
        = ((n : ℝ) * Partitions.part n) *
            Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [u]
    _ = (∑ m ∈ Finset.Icc 1 n,
            Sigma.sigmaR m * Partitions.part (n - m)) *
          Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [hrec]
    _ = ((∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m)) +
          Sigma.sigmaR n * Partitions.part 0) *
          Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [hsplit]
    _ = (∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m) *
              Real.exp (-C * Real.sqrt (n : ℝ))) +
          Sigma.sigmaR n * Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [Partitions.part_zero]
          rw [add_mul, Finset.sum_mul]
          ring
    _ = (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) +
          boundaryTerm n := by
          rw [hmain]
          rfl

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

section
/-!
# Barrier-package foundations (HR Stage I.5)

Definitions and the easy layers of the logarithmic-barrier route to two-sided boundedness
of `u` (route R6, audited): `kernelMass`/`kernelWindow`, the barriers `1 ∓ A/log(n+E)`,
the slack scale `1/(√n log²(n+E))`, the positive fixed window (from the banked
`erdos_kernel_window` + integral positivity), barrier range bounds, and boundary-vs-slack
negligibility (from the banked cube-decay lemma).  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Upper barrier `1 − A/log(n+E)`. -/
noncomputable def upperBarrier (A E : ℝ) (n : ℕ) : ℝ :=
  1 - A / Real.log ((n : ℝ) + E)

/-- The barrier slack scale `1/(√n·log²(n+E))`. -/
noncomputable def barrierSlack (E : ℝ) (n : ℕ) : ℝ :=
  1 / (Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2)

/-- **Positive fixed window**: some window `(a₀√n, b₀√n]` carries kernel mass `≥ μ > 0`
eventually. -/
theorem erdos_kernel_fixed_window_pos :
    ∃ a₀ b₀ μ : ℝ, 0 < a₀ ∧ a₀ < b₀ ∧ 0 < μ ∧
      ∀ᶠ n : ℕ in atTop, μ ≤ kernelWindow a₀ b₀ n := by
  have hC := C_pos
  -- the limit value: I := ∫_1^2 (π²/6) y e^{−(C/2)y} dy > 0
  have hIpos : 0 < Model.modelIntegral C 1 2 := by
    rw [Model.modelIntegral]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · -- integrability
      have hc : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
        have h1 : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y :=
          continuous_const.mul continuous_id
        have h2 : Continuous fun y : ℝ => Real.exp (-(C / 2) * y) :=
          Real.continuous_exp.comp (continuous_const.mul continuous_id)
        exact h1.mul h2
      exact hc.intervalIntegrable _ _
    · intro y hy
      have hy1 : (1 : ℝ) < y := hy.1
      have hπ : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
      have he : (0 : ℝ) < Real.exp (-(C / 2) * y) := Real.exp_pos _
      nlinarith [mul_pos (mul_pos hπ (by linarith : (0:ℝ) < y)) he]
    · norm_num
  refine ⟨1, 2, Model.modelIntegral C 1 2 / 2, one_pos, one_lt_two, by positivity, ?_⟩
  -- the window mass tends to the integral, so eventually exceeds half of it
  have hwin := Model.erdos_kernel_window (a := 1) (b := 2) zero_le_one one_lt_two
  have hev := (tendsto_order.1 hwin).1 (Model.modelIntegral C 1 2 / 2) (by linarith)
  filter_upwards [hev] with n hn
  exact hn.le

/-- Upper barrier eventually in `(0, 1]`. -/
lemma upperBarrier_eventually_pos_bdd {A E : ℝ} (hA : 0 < A) (hE : 3 ≤ E) :
    ∀ᶠ n : ℕ in atTop, 0 < upperBarrier A E n ∧ upperBarrier A E n ≤ 1 := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + E)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop
  have hev := hlog.eventually_gt_atTop A
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hlogpos : 0 < Real.log ((n : ℝ) + E) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have : (1 : ℝ) < (n : ℝ) + E := by linarith
    exact Real.log_pos this
  constructor
  · have : A / Real.log ((n : ℝ) + E) < 1 := by
      rw [div_lt_one hlogpos]
      exact hn
    rw [upperBarrier]
    linarith
  · rw [upperBarrier]
    have : 0 ≤ A / Real.log ((n : ℝ) + E) := by positivity
    linarith

/-- Barrier slack is eventually positive. -/
lemma barrierSlack_eventually_pos {E : ℝ} (hE : 3 ≤ E) :
    ∀ᶠ n : ℕ in atTop, 0 < barrierSlack E n := by
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hgt : (1 : ℝ) < (n : ℝ) + E := by linarith
  have hlogpos : 0 < Real.log ((n : ℝ) + E) := Real.log_pos hgt
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  rw [barrierSlack]
  positivity

/-- `n⁵·e^{−C√n} → 0`. -/
private lemma nat_pow5_mul_exp_neg_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => ((n : ℝ)) ^ 5 * Real.exp (-C * Real.sqrt (n : ℝ)))
      atTop (𝓝 0) := by
  have hC := C_pos
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 10).comp
    (Tendsto.const_mul_atTop hC
      (Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)))
  have hbase' : Tendsto
      (fun n : ℕ => (C * Real.sqrt (n : ℝ)) ^ 10 * Real.exp (-(C * Real.sqrt (n : ℝ))))
      atTop (𝓝 0) := by
    simpa [Function.comp] using hbase
  have hconst := hbase'.const_mul (1 / C ^ 10)
  rw [mul_zero] at hconst
  refine hconst.congr fun n => ?_
  have hsq : Real.sqrt (n : ℝ) ^ 10 = ((n : ℝ)) ^ 5 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul]
    congr 1
    exact Real.sq_sqrt (Nat.cast_nonneg n)
  have harg : -(C * Real.sqrt (n : ℝ)) = -C * Real.sqrt (n : ℝ) := by ring
  rw [mul_pow, hsq, harg]
  field_simp

/-- **Boundary is negligible against the slack**: `boundaryTerm n ≤ δ·barrierSlack E n`
eventually, for every `δ > 0`. -/
lemma boundaryTerm_le_barrierSlack {E δ : ℝ} (hE : 3 ≤ E) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, boundaryTerm n ≤ δ * barrierSlack E n := by
  have hC := C_pos
  have hev := (tendsto_order.1 nat_pow5_mul_exp_neg_sqrt_tendsto_zero).2
    (δ / 4) (by positivity)
  filter_upwards [hev, eventually_ge_atTop 1, eventually_ge_atTop ⌈E⌉₊]
    with n hn5 hn1 hnE
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hEn : E ≤ (n : ℝ) := le_trans (Nat.le_ceil E) (by exact_mod_cast hnE)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hgt1 : (1 : ℝ) < (n : ℝ) + E := by linarith
  have hlogpos : 0 < Real.log ((n : ℝ) + E) := Real.log_pos hgt1
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hEpos : 0 < Real.exp (-C * Real.sqrt (n : ℝ)) := Real.exp_pos _
  -- boundary ≤ n²·e^{−C√n}
  have hbd : boundaryTerm n ≤ (n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ)) := by
    rw [boundaryTerm]
    exact mul_le_mul_of_nonneg_right (sigmaR_le_square hn1) hEpos.le
  -- √n·log²(n+E) ≤ 4n³
  have hlog_le : Real.log ((n : ℝ) + E) ≤ 2 * (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (n : ℝ) + E)
    linarith
  have hs_le : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (n : ℝ) := Real.sqrt_sq hnpos.le
  have hfac : Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2 ≤ 4 * (n : ℝ) ^ 3 := by
    have hlogsq : (Real.log ((n : ℝ) + E)) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
      nlinarith [hlogpos.le, hlog_le]
    calc Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2
        ≤ (n : ℝ) * (4 * (n : ℝ) ^ 2) :=
          mul_le_mul hs_le hlogsq (by positivity) hnpos.le
      _ = 4 * (n : ℝ) ^ 3 := by ring
  -- assemble: boundary·(√n·log²) ≤ 4n⁵e^{−C√n} ≤ δ
  have hd_pos : 0 < Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2 := by positivity
  rw [barrierSlack, mul_one_div, le_div_iff₀ hd_pos]
  calc boundaryTerm n * (Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2)
      ≤ ((n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ))) *
          (Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2) :=
        mul_le_mul_of_nonneg_right hbd hd_pos.le
    _ ≤ ((n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ))) * (4 * (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = 4 * ((n : ℝ) ^ 5 * Real.exp (-C * Real.sqrt (n : ℝ))) := by ring
    _ ≤ 4 * (δ / 4) := by linarith [hn5]
    _ = δ := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Barrier gap on a positive kernel window (R6 lemma 4)

On the window `a₀√n < m ≤ b₀√n` the logarithmic barrier moves by at least a fixed
multiple of the slack: both

  `upperBarrier n − upperBarrier (n−m)` and `lowerBarrier (n−m) − lowerBarrier n`

equal `A/log(n−m+E) − A/log(n+E)`, and

  `log(n+E) − log(n−m+E) ≥ m/(n+E) ≥ (a₀/2)·(1/√n)`

(by `log r ≤ r − 1` on `r = (n−m+E)/(n+E)`), while the denominator product is at most
`log²(n+E)`.  Hence the gap is `≥ (A·a₀/2)·barrierSlack E n` eventually.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Core gap estimate: on the window, `A/log(n−m+E) − A/log(n+E) ≥ (A a₀/2)·slack`. -/
lemma barrier_core_gap_on_window
    {A E a₀ b₀ : ℝ} (hA : 0 < A) (hE : 3 ≤ E)
    (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      a₀ * Real.sqrt (n : ℝ) < (m : ℝ) →
      (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ) →
      A / Real.log (((n - m : ℕ) : ℝ) + E) - A / Real.log ((n : ℝ) + E)
        ≥ (A * a₀ / 2) * barrierSlack E n := by
  have hb₀ : 0 < b₀ := lt_trans ha₀ hab₀
  -- eventual regime: n ≥ 1, n ≥ E, 2b₀ ≤ √n
  have hev : ∀ᶠ n : ℕ in atTop,
      (1 ≤ n ∧ E ≤ (n : ℝ)) ∧ 2 * b₀ ≤ Real.sqrt (n : ℝ) := by
    have h1 := eventually_ge_atTop 1
    have h2 : ∀ᶠ n : ℕ in atTop, E ≤ (n : ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈E⌉₊] with n hn
      exact le_trans (Nat.le_ceil E) (by exact_mod_cast hn)
    have h3 : ∀ᶠ n : ℕ in atTop, 2 * b₀ ≤ Real.sqrt (n : ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈(2 * b₀) ^ 2⌉₊] with n hn
      have hcast : ((2 * b₀) ^ 2 : ℝ) ≤ (n : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
      have h2b : (0 : ℝ) ≤ 2 * b₀ := by positivity
      calc 2 * b₀ = Real.sqrt ((2 * b₀) ^ 2) := (Real.sqrt_sq h2b).symm
        _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hcast
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
    exact ⟨⟨hn1, hn2⟩, hn3⟩
  filter_upwards [hev] with n ⟨⟨hn1, hnE⟩, hsb⟩
  intro m hma hmb
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  -- m ≤ n/2 (window inside the left half)
  have hm_half : 2 * (m : ℝ) ≤ (n : ℝ) := by
    calc 2 * (m : ℝ) ≤ 2 * (b₀ * Real.sqrt (n : ℝ)) := by linarith
      _ = (2 * b₀) * Real.sqrt (n : ℝ) := by ring
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_right hsb hspos.le
      _ = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hm_le_n : m ≤ n := by
    have : (m : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hcast_sub : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm_le_n]
    ring
  -- positivity of the logs
  have hgt1 : (1 : ℝ) < (n : ℝ) + E := by linarith
  have hlogn : 0 < Real.log ((n : ℝ) + E) := Real.log_pos hgt1
  have hsubgt1 : (1 : ℝ) < ((n - m : ℕ) : ℝ) + E := by
    rw [hcast_sub]
    have : (n : ℝ) - (m : ℝ) ≥ (n : ℝ) / 2 := by linarith
    linarith
  have hlogsub : 0 < Real.log (((n - m : ℕ) : ℝ) + E) := Real.log_pos hsubgt1
  have hlog_mono : Real.log (((n - m : ℕ) : ℝ) + E) ≤ Real.log ((n : ℝ) + E) := by
    apply Real.log_le_log (by linarith)
    rw [hcast_sub]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  -- numerator bound: log(n+E) − log(n−m+E) ≥ m/(n+E)
  have hnum : Real.log ((n : ℝ) + E) - Real.log (((n - m : ℕ) : ℝ) + E)
      ≥ (m : ℝ) / ((n : ℝ) + E) := by
    -- log r ≤ r − 1 with r = (n−m+E)/(n+E)
    have hr_pos : 0 < (((n - m : ℕ) : ℝ) + E) / ((n : ℝ) + E) := by
      apply div_pos (by linarith) (by linarith)
    have hlogr := Real.log_le_sub_one_of_pos hr_pos
    have hlog_div : Real.log ((((n - m : ℕ) : ℝ) + E) / ((n : ℝ) + E))
        = Real.log (((n - m : ℕ) : ℝ) + E) - Real.log ((n : ℝ) + E) :=
      Real.log_div (by linarith) (by linarith)
    rw [hlog_div] at hlogr
    have hfrac : (((n - m : ℕ) : ℝ) + E) / ((n : ℝ) + E) - 1
        = -((m : ℝ) / ((n : ℝ) + E)) := by
      rw [hcast_sub]
      field_simp
      ring
    rw [hfrac] at hlogr
    linarith
  -- (a₀/2)·(1/√n) ≤ m/(n+E)
  have hm_lower : (a₀ / 2) * (1 / Real.sqrt (n : ℝ)) ≤ (m : ℝ) / ((n : ℝ) + E) := by
    have hden : (n : ℝ) + E ≤ 2 * (n : ℝ) := by linarith
    have hge : (a₀ * Real.sqrt (n : ℝ)) / (2 * (n : ℝ)) ≤ (m : ℝ) / ((n : ℝ) + E) :=
      div_le_div₀ (Nat.cast_nonneg m) hma.le (by linarith) hden
    have heq : (a₀ * Real.sqrt (n : ℝ)) / (2 * (n : ℝ))
        = (a₀ / 2) * (1 / Real.sqrt (n : ℝ)) := by
      have hss : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg n)
      field_simp
      nlinarith [hss]
    rw [← heq]
    exact hge
  -- assemble: gap = A·(log(n+E) − log(n−m+E))/(log(n−m+E)·log(n+E)) ≥ ...
  have hgap_eq : A / Real.log (((n - m : ℕ) : ℝ) + E) - A / Real.log ((n : ℝ) + E)
      = A * (Real.log ((n : ℝ) + E) - Real.log (((n - m : ℕ) : ℝ) + E)) /
          (Real.log (((n - m : ℕ) : ℝ) + E) * Real.log ((n : ℝ) + E)) := by
    field_simp
  rw [hgap_eq, ge_iff_le, barrierSlack]
  -- target: (A a₀/2)·(1/(√n log²(n+E))) ≤ A·num/(logsub·logn)
  have hden_le : Real.log (((n - m : ℕ) : ℝ) + E) * Real.log ((n : ℝ) + E)
      ≤ (Real.log ((n : ℝ) + E)) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hlog_mono hlogn.le
    nlinarith [this]
  have hnum_ge : (a₀ / 2) * (1 / Real.sqrt (n : ℝ))
      ≤ Real.log ((n : ℝ) + E) - Real.log (((n - m : ℕ) : ℝ) + E) :=
    le_trans hm_lower hnum
  calc (A * a₀ / 2) * (1 / (Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + E)) ^ 2))
      = A * ((a₀ / 2) * (1 / Real.sqrt (n : ℝ))) / (Real.log ((n : ℝ) + E)) ^ 2 := by
        field_simp
    _ ≤ A * (Real.log ((n : ℝ) + E) - Real.log (((n - m : ℕ) : ℝ) + E)) /
          (Real.log ((n : ℝ) + E)) ^ 2 := by
        gcongr
    _ ≤ A * (Real.log ((n : ℝ) + E) - Real.log (((n - m : ℕ) : ℝ) + E)) /
          (Real.log (((n - m : ℕ) : ℝ) + E) * Real.log ((n : ℝ) + E)) := by
        have hnumpos : 0 ≤ A * (Real.log ((n : ℝ) + E) -
            Real.log (((n - m : ℕ) : ℝ) + E)) := by
          have : 0 ≤ Real.log ((n : ℝ) + E) -
              Real.log (((n - m : ℕ) : ℝ) + E) := by linarith [hlog_mono]
          positivity
        gcongr

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Super/subharmonicity of the logarithmic barriers (R6 lemmas 5–6, conditional on rate)

Given the (yet-unbanked) critical mass rate in `o(slack)` form — for every `ρ > 0`,
eventually `|kernelMass n − 1| ≤ ρ·barrierSlack E n` — the kernel averages the barriers
strictly inward:

  `Σ W(n,m)·H₊(n−m) ≤ H₊(n) − δ·slack`   and   `Σ W(n,m)·H₋(n−m) ≥ H₋(n) + δ·slack`.

Split at the positive fixed window: off-window terms move the right way by barrier
monotonicity; window terms gain `c·slack` each (BarrierGap core, `c = a₀/2` at `A = 1`);
the mass error is absorbed by instantiating `ρ` small against `c·μ`.  The rate hypothesis is
the one remaining analytic brick (second-order cancellation — see HANDOFF design notes).
Opus-authored; CONDITIONAL on the rate hypothesis (no axioms — hypothesis-parameterized).
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `upperBarrier` is monotone in `n` (for `A > 0`, `E ≥ 3`). -/
lemma upperBarrier_mono {A E : ℝ} (hA : 0 < A) (hE : 3 ≤ E) :
    Monotone (upperBarrier A E) := by
  intro k l hkl
  have hk : (1 : ℝ) < (k : ℝ) + E := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hl : (1 : ℝ) < (l : ℝ) + E := by
    have : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    linarith
  have hlogk : 0 < Real.log ((k : ℝ) + E) := Real.log_pos hk
  have hlogl : 0 < Real.log ((l : ℝ) + E) := Real.log_pos hl
  have hmono : Real.log ((k : ℝ) + E) ≤ Real.log ((l : ℝ) + E) := by
    apply Real.log_le_log (by linarith)
    have : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
    linarith
  rw [upperBarrier, upperBarrier]
  have : A / Real.log ((l : ℝ) + E) ≤ A / Real.log ((k : ℝ) + E) :=
    div_le_div_of_nonneg_left hA.le hlogk hmono
  linarith

/-- `upperBarrier ≤ 1` always (for `A > 0`, `E ≥ 3`). -/
lemma upperBarrier_le_one {A E : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (n : ℕ) :
    upperBarrier A E n ≤ 1 := by
  have h1 : (1 : ℝ) < (n : ℝ) + E := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hlog : 0 < Real.log ((n : ℝ) + E) := Real.log_pos h1
  rw [upperBarrier]
  have : 0 ≤ A / Real.log ((n : ℝ) + E) := by positivity
  linarith

/-- The exact window/complement split of a kernel-weighted sum. -/
private lemma kernel_sum_split (a b : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * g (n - m))
      = (∑ m ∈ Finset.Icc 1 (n - 1),
          if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
          then erdosWeight n m * g (n - m) else 0)
        + (∑ m ∈ Finset.Icc 1 (n - 1),
          if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
          then 0 else erdosWeight n m * g (n - m)) := by
  classical
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  by_cases hwin : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
  · rw [if_pos hwin, if_pos hwin, add_zero]
  · rw [if_neg hwin, if_neg hwin, zero_add]

/--
**Upper barrier is superharmonic, conditional on the mass rate** (R6 lemma 5):
if `|kernelMass n − 1| ≤ ρ·barrierSlack E n` eventually, then for a suitable `A` the kernel
average of `upperBarrier A E` sits below `upperBarrier A E n − δ·slack`.
-/
lemma upperBarrier_one_pos {E : ℝ} (hE : 3 ≤ E) (k : ℕ) : 0 < upperBarrier 1 E k := by
  have hkE : (0:ℝ) < (k:ℝ) + E := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hlog : 1 < Real.log ((k:ℝ) + E) := by
    rw [Real.lt_log_iff_exp_lt hkE]
    have := Real.exp_one_lt_three
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [upperBarrier]
  have hdiv : 1 / Real.log ((k:ℝ) + E) < 1 := by rw [div_lt_one (by linarith)]; linarith
  linarith

theorem upperBarrier_kernel_superharmonic_of_rate
    {E : ℝ} (hE : 3 ≤ E)
    (hrate : ∀ ρ : ℝ, 0 < ρ →
      ∀ᶠ n : ℕ in atTop, |kernelMass n - 1| ≤ ρ * barrierSlack E n) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ (∀ k : ℕ, 0 < upperBarrier A E k) ∧
      ∀ᶠ n : ℕ in atTop,
        (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
          ≤ upperBarrier A E n - δ * barrierSlack E n := by
  classical
  obtain ⟨a₀, b₀, μ, ha₀, hab₀, hμ, hwinmass⟩ := erdos_kernel_fixed_window_pos
  have hA : (0 : ℝ) < 1 := one_pos
  set A : ℝ := 1 with hAdef
  set c : ℝ := A * a₀ / 2 with hcdef
  have hc : 0 < c := by rw [hcdef, hAdef]; positivity
  set ρ : ℝ := c * μ / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  refine ⟨A, c * μ - ρ, hA, by rw [hρdef]; nlinarith [mul_pos hc hμ],
    (fun k => by rw [hAdef]; exact upperBarrier_one_pos hE k), ?_⟩
  filter_upwards [barrier_core_gap_on_window hA hE ha₀ hab₀, hwinmass, hrate ρ hρ,
    barrierSlack_eventually_pos hE, upperBarrier_eventually_pos_bdd hA hE,
    eventually_ge_atTop 1] with n hgap hwin hr hsl hbdd hn1
  -- per-term bounds on the two pieces
  have hsplit := kernel_sum_split a₀ b₀ n (upperBarrier A E)
  have hwin_term : (∑ m ∈ Finset.Icc 1 (n - 1),
      if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
      then erdosWeight n m * upperBarrier A E (n - m) else 0)
      ≤ (upperBarrier A E n - c * barrierSlack E n) * kernelWindow a₀ b₀ n := by
    rw [kernelWindow, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro m hm
    by_cases hwinm : a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧
        (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
    · rw [if_pos hwinm, if_pos hwinm]
      have hW : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
      have hcore := hgap m hwinm.1 hwinm.2
      -- upperBarrier(n−m) ≤ upperBarrier n − c·slack
      have hble : upperBarrier A E (n - m) ≤ upperBarrier A E n - c * barrierSlack E n := by
        rw [upperBarrier, upperBarrier] at *
        rw [hcdef]
        linarith [hcore]
      calc erdosWeight n m * upperBarrier A E (n - m)
          ≤ erdosWeight n m * (upperBarrier A E n - c * barrierSlack E n) :=
            mul_le_mul_of_nonneg_left hble hW
        _ = (upperBarrier A E n - c * barrierSlack E n) * erdosWeight n m := by ring
    · rw [if_neg hwinm, if_neg hwinm, mul_zero]
  have hoff_term : (∑ m ∈ Finset.Icc 1 (n - 1),
      if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
      then 0 else erdosWeight n m * upperBarrier A E (n - m))
      ≤ upperBarrier A E n * (kernelMass n - kernelWindow a₀ b₀ n) := by
    have hKW : kernelMass n - kernelWindow a₀ b₀ n
        = ∑ m ∈ Finset.Icc 1 (n - 1),
            (if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
             then 0 else erdosWeight n m) := by
      rw [kernelMass, kernelWindow, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro m _hm
      by_cases hwinm : a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧
          (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
      · rw [if_pos hwinm, if_pos hwinm, sub_self]
      · rw [if_neg hwinm, if_neg hwinm, sub_zero]
    rw [hKW, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro m hm
    by_cases hwinm : a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧
        (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
    · rw [if_pos hwinm, if_pos hwinm, mul_zero]
    · rw [if_neg hwinm, if_neg hwinm]
      have hW : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
      have hmle : n - m ≤ n := Nat.sub_le n m
      have hmono := upperBarrier_mono hA hE hmle
      calc erdosWeight n m * upperBarrier A E (n - m)
          ≤ erdosWeight n m * upperBarrier A E n :=
            mul_le_mul_of_nonneg_left hmono hW
        _ = upperBarrier A E n * erdosWeight n m := by ring
  -- assemble
  have htotal : (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
      ≤ upperBarrier A E n * kernelMass n - c * barrierSlack E n * kernelWindow a₀ b₀ n := by
    rw [hsplit]
    have := add_le_add hwin_term hoff_term
    calc (∑ m ∈ Finset.Icc 1 (n - 1),
          if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
          then erdosWeight n m * upperBarrier A E (n - m) else 0)
        + (∑ m ∈ Finset.Icc 1 (n - 1),
          if a₀ * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ)
          then 0 else erdosWeight n m * upperBarrier A E (n - m))
        ≤ (upperBarrier A E n - c * barrierSlack E n) * kernelWindow a₀ b₀ n
          + upperBarrier A E n * (kernelMass n - kernelWindow a₀ b₀ n) := this
      _ = upperBarrier A E n * kernelMass n
          - c * barrierSlack E n * kernelWindow a₀ b₀ n := by ring
  -- mass error absorption: H·mass ≤ H + |mass−1| (|H| ≤ 1 here), window ≥ μ
  have hH1 : |upperBarrier A E n| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hbdd.1]
    · exact hbdd.2
  have hmass_abs : upperBarrier A E n * kernelMass n
      ≤ upperBarrier A E n + ρ * barrierSlack E n := by
    have h1 : upperBarrier A E n * kernelMass n
        = upperBarrier A E n + upperBarrier A E n * (kernelMass n - 1) := by ring
    rw [h1]
    have h2 : upperBarrier A E n * (kernelMass n - 1)
        ≤ |upperBarrier A E n * (kernelMass n - 1)| := le_abs_self _
    have h3 : |upperBarrier A E n * (kernelMass n - 1)|
        = |upperBarrier A E n| * |kernelMass n - 1| := abs_mul _ _
    have h4 : |upperBarrier A E n| * |kernelMass n - 1| ≤ 1 * (ρ * barrierSlack E n) := by
      apply mul_le_mul hH1 hr (abs_nonneg _) one_pos.le
    linarith
  have hwin_lower : c * barrierSlack E n * kernelWindow a₀ b₀ n
      ≥ c * barrierSlack E n * μ := by
    apply mul_le_mul_of_nonneg_left hwin
    positivity
  calc (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
      ≤ upperBarrier A E n * kernelMass n - c * barrierSlack E n * kernelWindow a₀ b₀ n :=
        htotal
    _ ≤ (upperBarrier A E n + ρ * barrierSlack E n) - c * barrierSlack E n * μ := by
        linarith [hmass_abs, hwin_lower]
    _ = upperBarrier A E n - (c * μ - ρ) * barrierSlack E n := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Boundedness of `u` by barrier induction (R6 lemmas 8–12, conditional)

Strong induction on the Erdős recurrence against super/subharmonic barriers:

* `u_upper_of_superharmonic` — if the upper barrier is superharmonic (with positive values)
  then `u n ≤ M·H₊(n)` for all `n`, hence `u` is eventually bounded above;
* `u_lower_of_subharmonic` — if the lower barrier is subharmonic then `c·H₋(n) ≤ u n` for
  all `n ≥ 1`, hence `liminf u > 0`.

Both take the harmonic inequality as a hypothesis (supplied conditionally-on-rate by
`BarrierHarmonic`; unconditionally once the mass-rate brick lands).  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/--
**Upper boundedness by barrier induction** (R6 lemma 8): a globally positive superharmonic
upper barrier dominates `u` up to a constant.
-/
theorem u_upper_of_superharmonic {A E δ : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (hδ : 0 < δ)
    (hpos : ∀ k : ℕ, 0 < upperBarrier A E k)
    (hsuper : ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
        ≤ upperBarrier A E n - δ * barrierSlack E n) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, u n ≤ M * upperBarrier A E n := by
  classical
  -- threshold where superharmonicity + boundary control + n ≥ 2 all hold
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hsuper
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (boundaryTerm_le_barrierSlack hE hδ)
  set N₀ : ℕ := max (max N₁ N₂) 2 with hN₀def
  -- M covers the initial segment and is ≥ 1
  have hne_range : (Finset.range (N₀ + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  set M₀ : ℝ := (Finset.range (N₀ + 1)).sup' hne_range
    (fun k => u k / upperBarrier A E k) with hM₀def
  set M : ℝ := max M₀ 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  refine ⟨M, hMpos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hsmall : n ≤ N₀
    · -- initial segment: M ≥ u n / H₊ n
      have hmem : n ∈ Finset.range (N₀ + 1) := Finset.mem_range.mpr (by omega)
      have hsup : u n / upperBarrier A E n ≤ M₀ :=
        Finset.le_sup' (fun k => u k / upperBarrier A E k) hmem
      have hHpos := hpos n
      have : u n / upperBarrier A E n ≤ M := le_trans hsup (le_max_left _ _)
      calc u n = (u n / upperBarrier A E n) * upperBarrier A E n := by
            field_simp
        _ ≤ M * upperBarrier A E n :=
            mul_le_mul_of_nonneg_right this hHpos.le
    · -- inductive step via the recurrence
      push_neg at hsmall
      have hn2 : 2 ≤ n := by omega
      have hnN₁ : N₁ ≤ n := by omega
      have hnN₂ : N₂ ≤ n := by omega
      have hrec := u_recurrence n hn2
      have hsup_n := hN₁ n hnN₁
      have hbdy_n := hN₂ n hnN₂
      -- termwise IH: u (n−m) ≤ M·H₊(n−m) for m ∈ Icc 1 (n−1)
      have hterm : (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m))
          ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * (M * upperBarrier A E (n - m)) := by
        refine Finset.sum_le_sum ?_
        intro m hm
        have hW : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        have hlt : n - m < n := by omega
        exact mul_le_mul_of_nonneg_left (ih (n - m) hlt) hW
      have hfactor : (∑ m ∈ Finset.Icc 1 (n - 1),
          erdosWeight n m * (M * upperBarrier A E (n - m)))
          = M * ∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * upperBarrier A E (n - m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        ring
      calc u n = (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m))
            + boundaryTerm n := hrec
        _ ≤ (∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * (M * upperBarrier A E (n - m)))
            + boundaryTerm n := by linarith [hterm]
        _ = M * (∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * upperBarrier A E (n - m))
            + boundaryTerm n := by rw [hfactor]
        _ ≤ M * (upperBarrier A E n - δ * barrierSlack E n)
            + δ * barrierSlack E n := by
            have h1 := mul_le_mul_of_nonneg_left hsup_n hMpos.le
            linarith [h1, hbdy_n]
        _ ≤ M * upperBarrier A E n := by
            have hslack_nonneg : 0 ≤ δ * barrierSlack E n := by
              -- δ > 0 and slack ≥ 0 for n in this regime (n ≥ 2)
              have h1 : (1 : ℝ) < (n : ℝ) + E := by
                have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
                linarith
              have hlog : 0 < Real.log ((n : ℝ) + E) := Real.log_pos h1
              have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
              rw [barrierSlack]
              positivity
            nlinarith [hslack_nonneg, hM1]

/-- Eventual upper bound (R6 lemma 9): `u n ≤ M` eventually. -/
theorem u_limsup_finite_of_superharmonic {A E δ : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (hδ : 0 < δ)
    (hpos : ∀ k : ℕ, 0 < upperBarrier A E k)
    (hsuper : ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
        ≤ upperBarrier A E n - δ * barrierSlack E n) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, u n ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := u_upper_of_superharmonic hA hE hδ hpos hsuper
  refine ⟨M, hMpos, ?_⟩
  filter_upwards with n
  calc u n ≤ M * upperBarrier A E n := hM n
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (upperBarrier_le_one hA hE n) hMpos.le
    _ = M := mul_one M

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: §5 the second-order divisor calc

`kernelMass n = ∑_{m=1}^{n-1} σ(m)/(n−m)·exp(−C(√n−√(n−m)))` versus
`kernelMassApprox2 n = (1/n)M₀(t)+(1/n²)M₁(t)−(C/(8n²√n))M₂(t)` at `t=λ/√n`.

Brick 1 here: `kernelMassApprox2 n = ∑' m, modelSummand n m`, where
`modelSummand n m = σ(m)·e^{−tm}·(1/n + m/n² − Cm²/(8n²√n))` — i.e. the moment package collapses
to a single divisor-weighted Lambert sum.  This is the object the per-term estimate
`erdosWeight_coef_second_order` (#97), multiplied by `σ(m)≥0`, is compared against.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

/-- **Mass rate in `o(slack)` form** (R6 input to the barriers): for every `ρ > 0`, eventually
`|kernelMass n − 1| ≤ ρ·barrierSlack E n`. The `1/n` rate (`kernelMass_sub_one_rate`) beats
`barrierSlack E n = 1/(√n·(log(n+E))²)` because `(log(n+E))² = o(√n)`. -/
theorem kernelMass_rate_vs_slack {E : ℝ} (hE : 3 ≤ E) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n : ℕ in Filter.atTop,
      |kernelMass n - 1| ≤ ρ * barrierSlack E n := by
  obtain ⟨K, hKpos, hK⟩ := kernelMass_sub_one_rate
  intro ρ hρ
  have hElt : (0:ℝ) < E := by linarith
  have hlittleo : (fun x : ℝ => Real.log x ^ (2:ℝ)) =o[Filter.atTop] (fun x => x ^ (1/2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num)
  have hevR : ∀ᶠ x : ℝ in Filter.atTop,
      (Real.log x) ^ 2 ≤ (ρ / (4 * K)) * x ^ (1/2 : ℝ) := by
    have h := hlittleo.def (show (0:ℝ) < ρ / (4 * K) by positivity)
    filter_upwards [h, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
    have e : Real.log x ^ (2:ℝ) = (Real.log x) ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, e, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    exact hx
  have hcomp : Filter.Tendsto (fun n : ℕ => (n:ℝ) + E) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ E tendsto_natCast_atTop_atTop
  filter_upwards [hK, hcomp.eventually hevR, Filter.eventually_ge_atTop (⌈E⌉₊ + 2)]
    with n hk hlogn hnE
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnE_le : (E:ℝ) ≤ (n:ℝ) := by
    have h1 : (⌈E⌉₊ : ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : ⌈E⌉₊ ≤ n)
    exact le_trans (Nat.le_ceil _) h1
  have hL : 0 < Real.log ((n:ℝ) + E) := Real.log_pos (by linarith)
  have hLsq : 0 < (Real.log ((n:ℝ) + E)) ^ 2 := by positivity
  have hsqrtn : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  -- (n+E)^{1/2} ≤ 2 √n
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hroot_le : ((n:ℝ) + E) ^ (1/2 : ℝ) ≤ 2 * Real.sqrt (n:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt ((n:ℝ) + E) ≤ Real.sqrt (2 * (n:ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt 2 * Real.sqrt (n:ℝ) := Real.sqrt_mul (by norm_num) _
      _ ≤ 2 * Real.sqrt (n:ℝ) := mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _)
  -- hence (log(n+E))² ≤ (ρ/(2K)) √n
  have hLbound : (Real.log ((n:ℝ) + E)) ^ 2 ≤ (ρ / (2 * K)) * Real.sqrt (n:ℝ) := by
    calc (Real.log ((n:ℝ) + E)) ^ 2 ≤ (ρ / (4 * K)) * ((n:ℝ) + E) ^ (1/2 : ℝ) := hlogn
      _ ≤ (ρ / (4 * K)) * (2 * Real.sqrt (n:ℝ)) :=
          mul_le_mul_of_nonneg_left hroot_le (by positivity)
      _ = (ρ / (2 * K)) * Real.sqrt (n:ℝ) := by ring
  -- assemble: K/n ≤ ρ·barrierSlack
  have hkey : K / (n:ℝ) ≤ ρ * barrierSlack E n := by
    rw [barrierSlack, mul_one_div, le_div_iff₀ (by positivity), div_mul_eq_mul_div,
      div_le_iff₀ hnpos]
    -- K * (√n * L²) ≤ ρ * n
    have hstep : K * (Real.sqrt (n:ℝ) * (Real.log ((n:ℝ) + E)) ^ 2)
        ≤ K * (Real.sqrt (n:ℝ) * ((ρ / (2 * K)) * Real.sqrt (n:ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLbound hsqrtn.le) hKpos.le
    have heq : K * (Real.sqrt (n:ℝ) * ((ρ / (2 * K)) * Real.sqrt (n:ℝ))) = (ρ / 2) * (n:ℝ) := by
      rw [show K * (Real.sqrt (n:ℝ) * ((ρ / (2 * K)) * Real.sqrt (n:ℝ)))
          = (K / (2 * K)) * ρ * (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) by ring,
        Real.mul_self_sqrt hnpos.le, show K / (2 * K) = 1 / 2 by field_simp]
      ring
    rw [heq] at hstep
    nlinarith [hstep, hρ, hnpos]
  exact le_trans hk hkey

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: §7 unconditional barrier bounds on `u`

The banked kernel-mass rate in `o(slack)` form (`kernelMass_rate_vs_slack`) discharges the
hypotheses of the conditional barrier theorems, giving unconditionally that the normalized
partition function `u` is bounded above (`u_limsup_finite`) and bounded below away from `0`
(`u_liminf_positive`).  Opus-authored.
-/

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **`u` is bounded above** (R6): unconditional, via the superharmonic upper barrier fed by the
`o(slack)` mass rate. -/
theorem u_limsup_finite : ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, u n ≤ M := by
  obtain ⟨A, δ, hA, hδ, hpos, hsuper⟩ :=
    upperBarrier_kernel_superharmonic_of_rate (le_refl (3:ℝ))
      (kernelMass_rate_vs_slack (le_refl (3:ℝ)))
  exact u_limsup_finite_of_superharmonic hA (le_refl (3:ℝ)) hδ hpos hsuper

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: the connection to `erdos_partition_limit_exists`

Instantiates the abstract `tendsto_of_killed_doeblin` for the concrete Erdős predecessor kernel
`killedKer Pker rnk J`, producing the full reduction:

  if the **Doeblin walls** hold for cofinitely many cutoffs `J` (finite-time overlap `δ > 0` on the
  high-rank band + vanishing escape mass), then the normalized partition sequence `u` converges to a
  positive limit — the existence of the Hardy–Ramanujan constant.

Every step here is mechanical (boundedness of `hitVal`, substochasticity of `Pker`, `rnk → atTop`,
row-stochasticity of the killed kernel for large `J`, the `KPowK L P̃`-harmonic identity); the two walls
bundled in `DoeblinWalls` are the only remaining analytic content (the Γ(2,C) convolution local-limit
wall — see HANDOFF UPDATE 8).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `u` is nonnegative (`n · p(n) · e^{…} ≥ 0`). -/
lemma u_nonneg (n : ℕ) : 0 ≤ u n := by
  unfold u
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (by unfold part; exact Nat.cast_nonneg _))
    (Real.exp_pos _).le

/-- `u` is globally bounded (eventual `limsup` bound padded by the finitely many initial terms). -/
lemma u_abs_le : ∃ Mu : ℝ, 0 ≤ Mu ∧ ∀ n, |u n| ≤ Mu := by
  obtain ⟨M, hMpos, hMev⟩ := u_limsup_finite
  obtain ⟨N, hN⟩ := eventually_atTop.1 hMev
  refine ⟨max M (∑ k ∈ Finset.range N, |u k|), le_trans hMpos.le (le_max_left _ _), fun n => ?_⟩
  by_cases h : n < N
  · exact le_trans (Finset.single_le_sum (f := fun k => |u k|) (fun k _ => abs_nonneg (u k))
      (Finset.mem_range.mpr h)) (le_max_right _ _)
  · rw [abs_of_nonneg (u_nonneg n)]
    exact le_trans (hN n (by omega)) (le_max_left _ _)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
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

/-- AM–GM exponent bound: `C√n − tn ≤ C²/(2t) − (t/2)n` for all `n` (`t > 0`),
since `(C − t√n)² ≥ 0`. -/
lemma modelSaddle_exponent_bound {t : ℝ} (ht : 0 < t) (n : ℕ) :
    C * Real.sqrt (n : ℝ) - t * (n : ℝ) ≤ C ^ 2 / (2 * t) - (t / 2) * (n : ℝ) := by
  have hsn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have ht2 : t ^ 2 * Real.sqrt (n : ℝ) ^ 2 = t ^ 2 * (n : ℝ) := by rw [hsn]
  rw [le_sub_iff_add_le, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t)]
  nlinarith [sq_nonneg (C - t * Real.sqrt (n : ℝ)), ht2]

/-- The model-saddle summand is summable for `t > 0`. -/
lemma summable_modelSaddleTerm {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ)) := by
  -- exp-only majorant: `exp(C√n−tn) ≤ exp(C²/2t)·exp(−t/2)^n`, geometric
  have hexp_summ :
      Summable (fun n : ℕ => Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ))) := by
    have hgeo :
        Summable (fun n : ℕ => Real.exp (C ^ 2 / (2 * t)) * Real.exp (-(t / 2)) ^ n) :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le
        (by rw [Real.exp_lt_one_iff]; linarith)).mul_left _
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) ?_ hgeo
    intro n
    calc Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ))
        ≤ Real.exp (C ^ 2 / (2 * t) - (t / 2) * (n : ℝ)) :=
          Real.exp_le_exp.mpr (modelSaddle_exponent_bound ht n)
      _ = Real.exp (C ^ 2 / (2 * t)) * Real.exp (-(t / 2)) ^ n := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  -- divide by `n`: `/n ≤ 1`, so termwise `≤` the exp-only majorant
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hexp_summ
  intro n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp only [Nat.cast_zero, div_zero]; positivity
  · rw [div_le_iff₀ (by exact_mod_cast hpos : (0 : ℝ) < (n : ℝ))]
    nlinarith [Real.exp_pos (C * Real.sqrt (n : ℝ) - t * (n : ℝ)),
      (by exact_mod_cast hpos : (1 : ℝ) ≤ (n : ℝ))]

/-- The model-saddle sum is strictly positive for `t > 0`. -/
lemma modelSaddle_pos {t : ℝ} (ht : 0 < t) : 0 < modelSaddle t := by
  unfold modelSaddle
  refine (summable_modelSaddleTerm ht).tsum_pos (fun n => by positivity) 1 ?_
  positivity

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Brick 3: Abelian comparison `P(e^{-t}) ~ a · modelSaddle` (HR constant)

From `u_n → a` (Erdős limit) and the global bound `u_abs_le`, the weighted sum
`∑ u_n w_n(t)` is Abelian-comparable to `a · ∑ w_n(t) = a · modelSaddle t`, where
`w_n(t) = e^{C√n − tn}/n`. Since `P = 1 + ∑ u_n w_n` and `modelSaddle → ∞`, this gives
`log P − log a − log modelSaddle → 0` (taking `modelSaddle → ∞` as a brick-4 hypothesis).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators
open AnalyticCombinatorics.Ch8.Partitions.Erdos

noncomputable section

/-- The model weight `w_n(t) = e^{C√n−tn}/n`; `n=0` value is `0`. -/
noncomputable def modelWeight (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ)

/-- Weighted sum `∑ u_n w_n(t)`. -/
noncomputable def weightedU (t : ℝ) : ℝ :=
  ∑' n : ℕ, u n * modelWeight t n

lemma modelWeight_nonneg (t : ℝ) (n : ℕ) : 0 ≤ modelWeight t n := by
  unfold modelWeight; positivity

lemma summable_modelWeight {t : ℝ} (ht : 0 < t) : Summable (modelWeight t) := by
  simpa [modelWeight] using summable_modelSaddleTerm ht

lemma modelSaddle_eq_tsum_modelWeight (t : ℝ) :
    modelSaddle t = ∑' n : ℕ, modelWeight t n := rfl

lemma summable_weightedU {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => u n * modelWeight t n) := by
  obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
  have hs : Summable (fun n : ℕ => Mu * modelWeight t n) :=
    (summable_modelWeight (t := t) ht).mul_left Mu
  refine hs.of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  have hw : 0 ≤ modelWeight t n := modelWeight_nonneg t n
  rw [abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right (hMu n) hw

lemma weightedU_term_eq_partLaplace_term {t : ℝ} {n : ℕ} (hn : n ≠ 0) :
    u n * modelWeight t n = part n * Real.exp (-(t * n)) := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  unfold u modelWeight
  field_simp
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring

lemma partLaplace_pos' {t : ℝ} (ht : 0 < t) : 0 < PartLaplace t := by
  unfold PartLaplace
  have hs := partLaplace_summable (t := t) ht
  have hnonneg : ∀ n : ℕ, 0 ≤ part n * Real.exp (-(t * n)) := fun n =>
    mul_nonneg (part_pos n).le (Real.exp_pos _).le
  have h0 : 0 < part 0 * Real.exp (-(t * (0 : ℕ))) := by
    simpa using mul_pos (part_pos 0) (Real.exp_pos (-(t * (0 : ℕ))))
  simpa using hs.tsum_pos hnonneg 0 h0

lemma partLaplace_eq_one_add_weightedU {t : ℝ} (ht : 0 < t) :
    PartLaplace t = 1 + weightedU t := by
  unfold PartLaplace weightedU
  have hp := partLaplace_summable (t := t) ht
  have hw := summable_weightedU (t := t) ht
  rw [hp.tsum_eq_zero_add, hw.tsum_eq_zero_add]
  have h0w : u 0 * modelWeight t 0 = 0 := by unfold u modelWeight; norm_num
  rw [h0w]
  have htail :
      (∑' n : ℕ, part (n + 1) * Real.exp (-(t * ((n + 1 : ℕ) : ℝ))))
        = ∑' n : ℕ, u (n + 1) * modelWeight t (n + 1) := by
    refine tsum_congr (fun n => ?_)
    rw [weightedU_term_eq_partLaplace_term (t := t) (n := n + 1) (by omega)]
  rw [htail]
  have hpart0 : part 0 * Real.exp (-(t * (0 : ℕ))) = 1 := by rw [part_zero]; norm_num
  rw [hpart0]; ring

/-- Finite head of model mass is negligible vs the (diverging) total. -/
lemma finite_modelWeight_head_div_tendsto_zero (N : ℕ)
    (hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (fun t : ℝ => (∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  set K : ℝ := ∑ n ∈ Finset.range N, Real.exp (C * Real.sqrt (n : ℝ)) / (n : ℝ) with hK
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ‖∑ n ∈ Finset.range N, modelWeight t n‖ ≤ K := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : (0 : ℝ) < t := ht
    have hnonneg_sum : 0 ≤ ∑ n ∈ Finset.range N, modelWeight t n :=
      Finset.sum_nonneg (fun n _ => modelWeight_nonneg t n)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg_sum, hK]
    refine Finset.sum_le_sum (fun n _ => ?_)
    unfold modelWeight
    rcases Nat.eq_zero_or_pos n with h0 | hnpos_nat
    · subst h0; simp
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
      have hexp_le : Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ))
          ≤ Real.exp (C * Real.sqrt (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [htpos.le, (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
      rw [div_eq_inv_mul, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
  have hK_div : Tendsto (fun t : ℝ => K / modelSaddle t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hMS_atTop
  have hft : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ‖(∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t‖ ≤ K / modelSaddle t := by
    filter_upwards [hbound, self_mem_nhdsWithin] with t hb ht
    have htpos : (0 : ℝ) < t := ht
    have hMSpos : 0 < modelSaddle t := modelSaddle_pos htpos
    have hb' : |∑ n ∈ Finset.range N, modelWeight t n| ≤ K := by rwa [Real.norm_eq_abs] at hb
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hMSpos]
    gcongr
  have hzero := squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) hft hK_div
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hzero

/-- Abelian ratio: `(∑ u_n w_n)/modelSaddle → a`. -/
lemma weightedU_div_modelSaddle_tendsto {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto u atTop (𝓝 a))
    (hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (fun t : ℝ => weightedU t / modelSaddle t) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hdiff : Tendsto
      (fun t : ℝ => (weightedU t - a * modelSaddle t) / modelSaddle t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hε4 : 0 < ε / 4 := by positivity
    have htail_event : ∀ᶠ n : ℕ in atTop, |u n - a| ≤ ε / 4 := by
      have hmetric := (Metric.tendsto_nhds.mp hlim) (ε / 4) hε4
      filter_upwards [hmetric] with n hn
      simpa [dist_eq_norm, Real.norm_eq_abs] using le_of_lt hn
    obtain ⟨N, hN⟩ := eventually_atTop.1 htail_event
    obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
    set B : ℝ := Mu + a with hB
    have hB0 : 0 ≤ B := by rw [hB]; linarith [hMu0, ha.le]
    have hhead0 := finite_modelWeight_head_div_tendsto_zero N hMS_atTop
    have hhead_small : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        B * ((∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t) ≤ ε / 2 := by
      have hmul : Tendsto
          (fun t : ℝ => B * ((∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using hhead0.const_mul B
      exact hmul.eventually_le_const hε2
    filter_upwards [self_mem_nhdsWithin, hhead_small] with t ht hhead_le
    have ht : 0 < t := ht
    have hWpos : 0 < modelSaddle t := modelSaddle_pos ht
    have hsW := summable_modelWeight (t := t) ht
    have hsu := summable_weightedU (t := t) ht
    have hsaw : Summable (fun n : ℕ => a * modelWeight t n) := hsW.mul_left a
    have hdiff_eq : weightedU t - a * modelSaddle t
        = ∑' n : ℕ, (u n - a) * modelWeight t n := by
      unfold weightedU
      rw [modelSaddle_eq_tsum_modelWeight, ← tsum_mul_left, ← hsu.tsum_sub hsaw]
      refine tsum_congr (fun n => ?_); ring
    have habs_summ : Summable (fun n : ℕ => |(u n - a) * modelWeight t n|) := by
      refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_
        ((summable_modelWeight (t := t) ht).mul_left B)
      intro n
      rw [abs_mul]
      have hw : 0 ≤ modelWeight t n := modelWeight_nonneg t n
      rw [abs_of_nonneg hw]
      have hu : |u n - a| ≤ B := by
        calc |u n - a| ≤ |u n| + |a| := abs_sub _ _
          _ ≤ Mu + a := by rw [abs_of_pos ha]; exact add_le_add (hMu n) le_rfl
      exact mul_le_mul_of_nonneg_right hu hw
    have habs_tsum : |∑' n : ℕ, (u n - a) * modelWeight t n|
        ≤ ∑' n : ℕ, |(u n - a) * modelWeight t n| := by
      have h2 : Summable (fun n : ℕ => ‖(u n - a) * modelWeight t n‖) := by
        simpa [Real.norm_eq_abs] using habs_summ
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm h2
    have hsplit_abs := Summable.sum_add_tsum_nat_add N habs_summ
    have hhead_bound : (∑ n ∈ Finset.range N, |(u n - a) * modelWeight t n|)
        ≤ B * ∑ n ∈ Finset.range N, modelWeight t n := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun n _ => ?_)
      rw [abs_mul]
      have hw : 0 ≤ modelWeight t n := modelWeight_nonneg t n
      rw [abs_of_nonneg hw]
      have hu : |u n - a| ≤ B := by
        calc |u n - a| ≤ |u n| + |a| := abs_sub _ _
          _ ≤ Mu + a := by rw [abs_of_pos ha]; exact add_le_add (hMu n) le_rfl
      exact mul_le_mul_of_nonneg_right hu hw
    have htail_summ : Summable (fun k : ℕ => modelWeight t (k + N)) :=
      (summable_nat_add_iff N).mpr (summable_modelWeight (t := t) ht)
    have htail_bound : (∑' k : ℕ, |(u (k + N) - a) * modelWeight t (k + N)|)
        ≤ (ε / 4) * (∑' k : ℕ, modelWeight t (k + N)) := by
      rw [← tsum_mul_left]
      apply Summable.tsum_le_tsum
      · intro k
        rw [abs_mul]
        have hw : 0 ≤ modelWeight t (k + N) := modelWeight_nonneg t (k + N)
        rw [abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_right (hN (k + N) (by omega)) hw
      · exact habs_summ.comp_injective (fun i j hij => by omega)
      · exact htail_summ.mul_left (ε / 4)
    have htail_weight_le_total : (∑' k : ℕ, modelWeight t (k + N)) ≤ modelSaddle t := by
      have hadd := Summable.sum_add_tsum_nat_add N (summable_modelWeight (t := t) ht)
      have hcomm : (∑' k : ℕ, modelWeight t (k + N)) = ∑' k : ℕ, modelWeight t (N + k) := by
        refine tsum_congr (fun k => ?_); rw [add_comm]
      rw [hcomm, modelSaddle_eq_tsum_modelWeight]
      have hfin_nonneg : 0 ≤ ∑ n ∈ Finset.range N, modelWeight t n :=
        Finset.sum_nonneg (fun n _ => modelWeight_nonneg t n)
      linarith [hadd]
    have htotal_abs : (∑' n : ℕ, |(u n - a) * modelWeight t n|)
        ≤ B * (∑ n ∈ Finset.range N, modelWeight t n) + (ε / 4) * modelSaddle t := by
      calc (∑' n : ℕ, |(u n - a) * modelWeight t n|)
          = (∑ n ∈ Finset.range N, |(u n - a) * modelWeight t n|)
            + ∑' k : ℕ, |(u (k + N) - a) * modelWeight t (k + N)| := hsplit_abs.symm
        _ ≤ B * (∑ n ∈ Finset.range N, modelWeight t n)
            + (ε / 4) * (∑' k : ℕ, modelWeight t (k + N)) := add_le_add hhead_bound htail_bound
        _ ≤ B * (∑ n ∈ Finset.range N, modelWeight t n) + (ε / 4) * modelSaddle t := by
            gcongr
    have hratio_bound : |(weightedU t - a * modelSaddle t) / modelSaddle t| < ε := by
      rw [abs_div, abs_of_pos hWpos]
      calc |weightedU t - a * modelSaddle t| / modelSaddle t
          ≤ (∑' n : ℕ, |(u n - a) * modelWeight t n|) / modelSaddle t := by
            rw [hdiff_eq]; exact div_le_div_of_nonneg_right habs_tsum hWpos.le
        _ ≤ (B * (∑ n ∈ Finset.range N, modelWeight t n) + (ε / 4) * modelSaddle t)
              / modelSaddle t := div_le_div_of_nonneg_right htotal_abs hWpos.le
        _ = B * ((∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t) + ε / 4 := by
            field_simp [hWpos.ne']
        _ ≤ ε / 2 + ε / 4 := add_le_add hhead_le le_rfl
        _ < ε := by linarith
    rw [dist_eq_norm, Real.norm_eq_abs, sub_zero]
    exact hratio_bound
  refine hdiff.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hWpos : modelSaddle t ≠ 0 := (modelSaddle_pos ht).ne'
  field_simp [hWpos]

/-- **Brick 3.** `log P(e^{-t}) − log a − log(modelSaddle t) → 0` (given `modelSaddle → ∞`). -/
theorem partLaplace_log_sub_modelSaddle_tendsto {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto u atTop (𝓝 a))
    (hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (fun t : ℝ => Real.log (PartLaplace t) - Real.log a - Real.log (modelSaddle t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hW := weightedU_div_modelSaddle_tendsto ha hlim hMS_atTop
  have hInvW : Tendsto (fun t : ℝ => 1 / modelSaddle t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hMS_atTop
  have hratioP : Tendsto (fun t : ℝ => PartLaplace t / (a * modelSaddle t))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hsum : Tendsto (fun t : ℝ => 1 / modelSaddle t + weightedU t / modelSaddle t)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 + a)) := hInvW.add hW
    have hscaled := hsum.const_mul (1 / a)
    have htarget : Tendsto
        (fun t : ℝ => 1 / a * (1 / modelSaddle t + weightedU t / modelSaddle t))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by simpa [ha.ne'] using hscaled
    refine htarget.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hWpos : modelSaddle t ≠ 0 := (modelSaddle_pos ht).ne'
    rw [partLaplace_eq_one_add_weightedU ht]
    field_simp [ha.ne', hWpos]
  have hlog : Tendsto (fun t : ℝ => Real.log (PartLaplace t / (a * modelSaddle t)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
    simpa using hcont.comp hratioP
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hPpos : 0 < PartLaplace t := partLaplace_pos' ht
  have hWpos : 0 < modelSaddle t := modelSaddle_pos ht
  rw [Real.log_div hPpos.ne' (mul_ne_zero ha.ne' hWpos.ne'), Real.log_mul ha.ne' hWpos.ne']
  ring

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
noncomputable section

open Filter Finset Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology Interval

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

set_option maxHeartbeats 1000000

private lemma pairwise_disjoint_Ioc_mul_nat_succ {t : ℝ} (ht : 0 ≤ t) :
    Pairwise (Disjoint on fun k : ℕ =>
      Set.Ioc (t * (k : ℝ)) (t * ((k + 1 : ℕ) : ℝ))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : i + 1 ≤ j := by omega
    have hreal : (((i + 1 : ℕ) : ℝ) ≤ (j : ℝ)) := by
      exact_mod_cast hnat
    have hle : t * ((i + 1 : ℕ) : ℝ) ≤ t * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hreal ht
    exact not_lt_of_ge (hxi.2.trans hle) hxj.1
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : j + 1 ≤ i := by omega
    have hreal : (((j + 1 : ℕ) : ℝ) ≤ (i : ℝ)) := by
      exact_mod_cast hnat
    have hle : t * ((j + 1 : ℕ) : ℝ) ≤ t * (i : ℝ) :=
      mul_le_mul_of_nonneg_left hreal ht
    exact not_lt_of_ge (hxj.2.trans hle) hxi.1

private lemma iUnion_Ioc_mul_nat_succ_eq_Ioi {t : ℝ} (ht : 0 < t) :
    (⋃ k : ℕ, Set.Ioc (t * (k : ℝ)) (t * ((k + 1 : ℕ) : ℝ))) =
      Set.Ioi (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    have hk_nonneg : 0 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.zero_le k)
    exact (mul_nonneg ht.le hk_nonneg).trans_lt hk.1
  · intro hx
    let y : ℝ := x / t
    have hy_pos : 0 < y := by
      dsimp [y]
      exact div_pos hx ht
    let n : ℕ := Nat.ceil y
    have hn_pos : 0 < n := by
      have : 0 < Nat.ceil y := (Nat.ceil_pos (a := y)).mpr hy_pos
      simpa [n] using this
    let k : ℕ := n - 1
    have hk_succ : k + 1 = n := by
      dsimp [k]
      omega
    have hlt_nat : k < Nat.ceil y := by
      dsimp [k, n]
      omega
    have hk_lt_y : ((k : ℕ) : ℝ) < y :=
      (Nat.lt_ceil (a := y) (n := k)).mp hlt_nat
    have hy_le_n : y ≤ (n : ℝ) := by
      have hnn : Nat.ceil y ≤ n := by
        simp [n]
      exact (Nat.ceil_le (a := y) (n := n)).mp hnn
    have hy_le_succ : y ≤ (((k + 1 : ℕ) : ℝ)) := by
      simpa [hk_succ] using hy_le_n
    have hmul : t * y = x := by
      dsimp [y]
      field_simp [ht.ne']
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    rw [← hmul]
    constructor
    · exact mul_lt_mul_of_pos_left hk_lt_y ht
    · exact mul_le_mul_of_nonneg_left hy_le_succ ht.le

theorem riemann_sum_Ioi_sub_integral_bound
    {f f' : ℝ → ℝ} {M η : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)
    (hf'int : IntegrableOn f' (Set.Ioi 0))
    (hfint : IntegrableOn f (Set.Ioi 0))
    (hbdd : ∀ x : ℝ, 0 < x → x ≤ η → |f x| ≤ M) :
    ∀ t : ℝ, 0 < t → t < η →
      |(∑' k : ℕ, if k = 0 then 0 else f (t * (k : ℝ)))
        - (1 / t) * ∫ x in Set.Ioi 0, f x| ≤
          (∫ x in Set.Ioi 0, |f' x|) + M := by
  intro t ht htη
  classical

  let a : ℕ → ℝ := fun k : ℕ => t * (k : ℝ)
  let b : ℕ → ℝ := fun k : ℕ => t * ((k + 1 : ℕ) : ℝ)
  let cell : ℕ → Set ℝ := fun k : ℕ => Set.Ioc (a k) (b k)
  let A : ℕ → ℝ := fun k : ℕ => if k = 0 then 0 else f (a k)
  let B : ℕ → ℝ := fun k : ℕ => ∫ x in cell k, f x
  let D : ℕ → ℝ := fun k : ℕ => ∫ x in cell k, |f' x|
  let G : ℕ → ℝ := fun k : ℕ => (if k = 0 then M * t else 0) + t * D k

  have hUnion : (⋃ k : ℕ, cell k) = Set.Ioi (0 : ℝ) := by
    simpa [cell, a, b] using iUnion_Ioc_mul_nat_succ_eq_Ioi (t := t) ht
  have hmeas : ∀ k : ℕ, MeasurableSet (cell k) := by
    intro k
    simp [cell, a, b]
  have hpair : Pairwise (Disjoint on cell) := by
    simpa [cell, a, b] using pairwise_disjoint_Ioc_mul_nat_succ (t := t) ht.le

  have hf'int_abs : IntegrableOn (fun x : ℝ => |f' x|) (Set.Ioi (0 : ℝ)) := by
    simpa [Real.norm_eq_abs] using hf'int.norm

  have hcells_f : HasSum B (∫ x in Set.Ioi (0 : ℝ), f x) := by
    have h_int_union : IntegrableOn f (⋃ k : ℕ, cell k) := by
      simpa [hUnion] using hfint
    simpa [B, hUnion] using
      (hasSum_integral_iUnion (μ := volume) (f := f) hmeas hpair h_int_union)

  have hcells_D : HasSum D (∫ x in Set.Ioi (0 : ℝ), |f' x|) := by
    have h_int_union :
        IntegrableOn (fun x : ℝ => |f' x|) (⋃ k : ℕ, cell k) := by
      simpa [hUnion] using hf'int_abs
    simpa [D, hUnion] using
      (hasSum_integral_iUnion
        (μ := volume) (f := fun x : ℝ => |f' x|) hmeas hpair h_int_union)

  have hD_nonneg : ∀ k : ℕ, 0 ≤ D k := by
    intro k
    dsimp [D]
    exact integral_nonneg (fun x : ℝ => abs_nonneg (f' x))

  have hab_ab : ∀ k : ℕ, a k ≤ b k := by
    intro k
    dsimp [a, b]
    have hnat : k ≤ k + 1 := Nat.le_succ k
    have hreal : ((k : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_left hreal ht.le

  have hpos_a : ∀ k : ℕ, k ≠ 0 → 0 < a k := by
    intro k hk
    dsimp [a]
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    exact mul_pos ht hkpos

  have hpoint :
      ∀ (k : ℕ), k ≠ 0 → ∀ x : ℝ, x ∈ cell k → |f x - f (a k)| ≤ D k := by
    intro k hk x hx
    have ha_pos : 0 < a k := hpos_a k hk
    have hax : a k ≤ x := le_of_lt hx.1
    have hxb : x ≤ b k := hx.2
    have hderiv' : ∀ y ∈ Set.uIcc (a k) x, HasDerivAt f (f' y) y := by
      intro y hy
      have hy' : y ∈ Set.Icc (a k) x := by
        simpa [Set.uIcc_of_le hax] using hy
      exact hderiv y (ha_pos.trans_le hy'.1)
    have hint : IntervalIntegrable f' volume (a k) x := by
      have hsub : Set.uIcc (a k) x ⊆ Set.Ioi (0 : ℝ) := by
        intro y hy
        have hy' : y ∈ Set.Icc (a k) x := by
          simpa [Set.uIcc_of_le hax] using hy
        exact ha_pos.trans_le hy'.1
      exact (hf'int.mono_set hsub).intervalIntegrable
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := f) (f' := f') (a := a k) (b := x) hderiv' hint
    have hnorm1 : |f x - f (a k)| ≤ ∫ u in a k..x, |f' u| := by
      rw [← hFTC]
      exact intervalIntegral.abs_integral_le_integral_abs
        (μ := volume) (f := f') hax
    have hint_ab : IntervalIntegrable f' volume (a k) (b k) := by
      have hsub : Set.uIcc (a k) (b k) ⊆ Set.Ioi (0 : ℝ) := by
        intro y hy
        have hy' : y ∈ Set.Icc (a k) (b k) := by
          simpa [Set.uIcc_of_le (hab_ab k)] using hy
        exact ha_pos.trans_le hy'.1
      exact (hf'int.mono_set hsub).intervalIntegrable
    have hint_abs_ab :
        IntervalIntegrable (fun u : ℝ => |f' u|) volume (a k) (b k) :=
      hint_ab.abs
    have hmono :
        ∫ u in a k..x, |f' u| ≤ ∫ u in a k..b k, |f' u| := by
      exact intervalIntegral.integral_mono_interval
        (μ := volume) (f := fun u : ℝ => |f' u|)
        (a := a k) (b := x) (c := a k) (d := b k)
        le_rfl hax hxb
        (Eventually.of_forall (fun u : ℝ => abs_nonneg (f' u)))
        hint_abs_ab
    have hright_eq : ∫ u in a k..b k, |f' u| = D k := by
      rw [intervalIntegral.integral_of_le (hab_ab k)]
    exact hnorm1.trans (hmono.trans_eq hright_eq)

  have hhead_interval : |∫ x in (0 : ℝ)..t, f x| ≤ M * t := by
    have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) t, ‖f x‖ ≤ M := by
      intro x hx
      have hx' : x ∈ Set.Ioc (0 : ℝ) t := by
        simpa [Set.uIoc_of_le ht.le] using hx
      simpa [Real.norm_eq_abs] using hbdd x hx'.1 (hx'.2.trans htη.le)
    have hnorm :
        ‖∫ x in (0 : ℝ)..t, f x‖ ≤ M * |t - (0 : ℝ)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := t) (C := M) (f := f) hbound
    simpa [Real.norm_eq_abs, abs_of_pos ht] using hnorm

  have hcell_error : ∀ k : ℕ, |t * A k - B k| ≤ G k := by
    intro k
    by_cases hk : k = 0
    · subst k
      have hB0_eq : B 0 = ∫ x in (0 : ℝ)..t, f x := by
        dsimp [B, cell, a, b]
        rw [intervalIntegral.integral_of_le ht.le]
        simp
      calc
        |t * A 0 - B 0| = |B 0| := by
          simp [A]
        _ = |∫ x in (0 : ℝ)..t, f x| := by
          rw [hB0_eq]
        _ ≤ M * t := hhead_interval
        _ ≤ M * t + t * D 0 := by
          exact le_add_of_nonneg_right (mul_nonneg ht.le (hD_nonneg 0))
        _ = G 0 := by
          simp [G]
    · have hB_eq : B k = ∫ x in a k..b k, f x := by
        dsimp [B, cell]
        rw [intervalIntegral.integral_of_le (hab_ab k)]
      have hconst : (∫ x in a k..b k, A k) = t * A k := by
        rw [intervalIntegral.integral_const]
        have hba : b k - a k = t := by
          dsimp [a, b]
          push_cast
          ring
        rw [hba]
        simp [smul_eq_mul]
      have hf_interval : IntervalIntegrable f volume (a k) (b k) := by
        have hsub : Set.uIcc (a k) (b k) ⊆ Set.Ioi (0 : ℝ) := by
          intro y hy
          have hy' : y ∈ Set.Icc (a k) (b k) := by
            simpa [Set.uIcc_of_le (hab_ab k)] using hy
          exact (hpos_a k hk).trans_le hy'.1
        exact (hfint.mono_set hsub).intervalIntegrable
      have hconst_int :
          IntervalIntegrable (fun _ : ℝ => A k) volume (a k) (b k) :=
        intervalIntegrable_const
      have hdiff :
          (∫ x in a k..b k, f x - A k) =
            (∫ x in a k..b k, f x) - (∫ x in a k..b k, A k) := by
        exact intervalIntegral.integral_sub hf_interval hconst_int
      have hbound_int : ∀ x ∈ Set.uIoc (a k) (b k), ‖f x - A k‖ ≤ D k := by
        intro x hx
        have hxcell : x ∈ cell k := by
          simpa [cell, Set.uIoc_of_le (hab_ab k)] using hx
        simpa [A, hk, Real.norm_eq_abs] using hpoint k hk x hxcell
      have hnorm_bound :
          ‖∫ x in a k..b k, f x - A k‖ ≤ D k * |b k - a k| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := a k) (b := b k) (C := D k)
          (f := fun x : ℝ => f x - A k) hbound_int
      have hrepr :
          t * A k - B k = - (∫ x in a k..b k, f x - A k) := by
        rw [hB_eq, ← hconst, hdiff]
        ring
      have habs : |b k - a k| = t := by
        have hba : b k - a k = t := by
          dsimp [a, b]
          push_cast
          ring
        rw [hba, abs_of_pos ht]
      have hmain : |t * A k - B k| ≤ t * D k := by
        calc
          |t * A k - B k| = ‖∫ x in a k..b k, f x - A k‖ := by
            rw [hrepr, Real.norm_eq_abs, abs_neg]
          _ ≤ D k * |b k - a k| := hnorm_bound
          _ = t * D k := by
            rw [habs]
            ring
      calc
        |t * A k - B k| ≤ t * D k := hmain
        _ = G k := by
          simp [G, hk]

  have hsumm_B : Summable B := hcells_f.summable
  have hhas_tD :
      HasSum (fun k : ℕ => t * D k)
        (t * ∫ x in Set.Ioi (0 : ℝ), |f' x|) := by
    have h := HasSum.const_smul t hcells_D
    simpa [smul_eq_mul] using h
  have hsingle : HasSum (fun k : ℕ => if k = 0 then M * t else 0) (M * t) :=
    hasSum_ite_eq (0 : ℕ) (M * t)
  have hhas_G :
      HasSum G (M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x|) := by
    have h := hsingle.add hhas_tD
    simpa [G, add_comm, add_left_comm, add_assoc] using h

  have hsumm_abs_error : Summable (fun k : ℕ => |t * A k - B k|) :=
    Summable.of_nonneg_of_le
      (fun k : ℕ => abs_nonneg (t * A k - B k))
      (fun k : ℕ => hcell_error k)
      hhas_G.summable
  have hsumm_error : Summable (fun k : ℕ => t * A k - B k) :=
    Summable.of_abs hsumm_abs_error

  have hsumm_tA : Summable (fun k : ℕ => t * A k) := by
    have h := hsumm_error.add hsumm_B
    refine h.congr ?_
    intro k
    ring

  have hsumm_A : Summable A := by
    have h := Summable.const_smul (1 / t) hsumm_tA
    refine h.congr ?_
    intro k
    change (1 / t) * (t * A k) = A k
    field_simp [ht.ne']

  have hhas_tA :
      HasSum (fun k : ℕ => t * A k) (t * (∑' k : ℕ, A k)) := by
    have h := HasSum.const_smul t hsumm_A.hasSum
    simpa [smul_eq_mul] using h

  have hhas_error :
      HasSum (fun k : ℕ => t * A k - B k)
        (t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x) :=
    hhas_tA.sub hcells_f

  have herror_eq :
      (∑' k : ℕ, (t * A k - B k)) =
        t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x :=
    HasSum.tsum_eq hhas_error

  have hsum_abs_has :
      HasSum (fun k : ℕ => |t * A k - B k|)
        (∑' k : ℕ, |t * A k - B k|) :=
    hsumm_abs_error.hasSum

  have habs_tsum :
      |∑' k : ℕ, (t * A k - B k)|
        ≤ ∑' k : ℕ, |t * A k - B k| := by
    have hupper :
        (∑' k : ℕ, (t * A k - B k))
          ≤ ∑' k : ℕ, |t * A k - B k| := by
      exact hasSum_le
        (fun k : ℕ => le_abs_self (t * A k - B k))
        hsumm_error.hasSum hsum_abs_has
    have hlower :
        -(∑' k : ℕ, |t * A k - B k|)
          ≤ ∑' k : ℕ, (t * A k - B k) := by
      have hneg :
          HasSum (fun k : ℕ => - |t * A k - B k|)
            (-(∑' k : ℕ, |t * A k - B k|)) :=
        hsum_abs_has.neg
      exact hasSum_le
        (fun k : ℕ => neg_abs_le (t * A k - B k))
        hneg hsumm_error.hasSum
    exact abs_le.mpr ⟨hlower, hupper⟩

  have habs_le_G :
      (∑' k : ℕ, |t * A k - B k|)
        ≤ M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x| := by
    exact hasSum_le
      (fun k : ℕ => hcell_error k)
      hsum_abs_has hhas_G

  have hscaled :
      |t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x|
        ≤ M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x| := by
    calc
      |t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x|
          = |∑' k : ℕ, (t * A k - B k)| := by
            rw [← herror_eq]
      _ ≤ ∑' k : ℕ, |t * A k - B k| := habs_tsum
      _ ≤ M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x| := habs_le_G

  have htinv_pos : 0 < 1 / t := one_div_pos.mpr ht

  change
    |(∑' k : ℕ, A k) - (1 / t) * ∫ x in Set.Ioi (0 : ℝ), f x| ≤
      (∫ x in Set.Ioi (0 : ℝ), |f' x|) + M

  calc
    |(∑' k : ℕ, A k) - (1 / t) * ∫ x in Set.Ioi (0 : ℝ), f x|
        = (1 / t) *
            |t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x| := by
          have hscale :
              (∑' k : ℕ, A k) - (1 / t) * ∫ x in Set.Ioi (0 : ℝ), f x =
                (1 / t) *
                  (t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x) := by
            field_simp [ht.ne']
          rw [hscale, abs_mul, abs_of_pos htinv_pos]
    _ ≤ (1 / t) *
          (M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x|) :=
          mul_le_mul_of_nonneg_left hscaled htinv_pos.le
    _ = (∫ x in Set.Ioi (0 : ℝ), |f' x|) + M := by
          calc
            (1 / t) * (M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x|)
                = (1 / t) *
                    (t * (M + ∫ x in Set.Ioi (0 : ℝ), |f' x|)) := by
                  ring
            _ = M + ∫ x in Set.Ioi (0 : ℝ), |f' x| := by
                  field_simp [ht.ne']
            _ = (∫ x in Set.Ioi (0 : ℝ), |f' x|) + M := by
                  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Model-saddle integrand: density + derivative (HR brick 4, integral comparison)

`saddleDensity t x = e^{C√x − tx}/x` is the continuous density whose `∫_{Ioi 1}` the
discrete `modelSaddle` sum is compared against (via `riemann_sum_Ioi_sub_integral_bound`,
applied to the shift `x ↦ saddleDensity t (x+1)` to avoid the `1/x` singularity at `0`).

This file establishes the density and its derivative
`saddleDensity'(t,x) = saddleDensity t x · (C/(2√x) − t − 1/x)`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology Real MeasureTheory
open AnalyticCombinatorics.Ch8.Partitions.Erdos

noncomputable section

/-- Continuous density `e^{C√x − tx}/x`. -/
noncomputable def saddleDensity (t x : ℝ) : ℝ :=
  Real.exp (C * Real.sqrt x - t * x) / x

/-- Derivative of the model-saddle density on `x > 0`. -/
lemma saddleDensity_hasDerivAt {t x : ℝ} (hx : 0 < x) :
    HasDerivAt (saddleDensity t)
      (saddleDensity t x * (C / (2 * Real.sqrt x) - t - 1 / x)) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsne : Real.sqrt x ≠ 0 := ne_of_gt hsqrtpos
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hxne
  have h2 : HasDerivAt (fun y : ℝ => t * y) t x := by simpa using (hasDerivAt_id x).const_mul t
  have hg : HasDerivAt (fun y : ℝ => C * Real.sqrt y - t * y)
      (C * (1 / (2 * Real.sqrt x)) - t) x := (hsqrt.const_mul C).sub h2
  have hnum := hg.exp
  have hdiv := hnum.div (hasDerivAt_id x) hxne
  simp only [id_eq] at hdiv
  convert hdiv using 1
  simp only [saddleDensity]
  field_simp

/-- Real-`y` AM–GM exponent bound: `C√y − sy ≤ C²/(2s) − (s/2)y` for `y ≥ 0`, `s > 0`. -/
lemma saddle_exponent_bound_real {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 ≤ y) :
    C * Real.sqrt y - s * y ≤ C ^ 2 / (2 * s) - (s / 2) * y := by
  have hsy : s ^ 2 * Real.sqrt y ^ 2 = s ^ 2 * y := by rw [Real.sq_sqrt hy]
  rw [le_sub_iff_add_le, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s)]
  nlinarith [sq_nonneg (C - s * Real.sqrt y), hsy]

/-- The shifted density `x ↦ saddleDensity s (x+1)` is integrable on `(0,∞)` (`s > 0`).
The shift removes the `1/x` singularity, and the integrand decays by the exponent bound. -/
lemma integrableOn_saddleDensity_shift {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => saddleDensity s (x + 1)) (Set.Ioi (0 : ℝ)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => saddleDensity s (x + 1))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    unfold saddleDensity
    fun_prop
  have hdom : IntegrableOn
      (fun x : ℝ => Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2) * (x + 1))) (Set.Ioi 0) := by
    have hbase : IntegrableOn (fun x : ℝ => Real.exp (-(s / 2) * x)) (Set.Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (half_pos hs)
    have h2 : IntegrableOn
        (fun x : ℝ => (Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2))) * Real.exp (-(s / 2) * x))
        (Set.Ioi 0) :=
      hbase.const_mul (Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2)))
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp only [← Real.exp_add]
    congr 1
    ring
  refine Integrable.mono' hdom hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  have hx0 : 0 < x := hx
  have hx1 : (1 : ℝ) ≤ x + 1 := by linarith
  have hden : (0 : ℝ) < x + 1 := by linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by unfold saddleDensity; exact div_nonneg (Real.exp_pos _).le hden.le)]
  unfold saddleDensity
  calc Real.exp (C * Real.sqrt (x + 1) - s * (x + 1)) / (x + 1)
      ≤ Real.exp (C * Real.sqrt (x + 1) - s * (x + 1)) := by
        rw [div_le_iff₀ hden]
        nlinarith [Real.exp_pos (C * Real.sqrt (x + 1) - s * (x + 1)), hx1]
    _ ≤ Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2) * (x + 1)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have := saddle_exponent_bound_real hs (y := x + 1) (by linarith)
        linarith

/-- Derivative of the shifted density (chain rule with `y ↦ y+1`). -/
lemma saddleDensity_shift_hasDerivAt {s x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun y : ℝ => saddleDensity s (y + 1))
      (saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1))) x := by
  have hxp1 : 0 < x + 1 := by linarith
  have h := (saddleDensity_hasDerivAt (t := s) hxp1).comp x ((hasDerivAt_id x).add_const 1)
  simpa using h

/-- The shifted-density derivative is integrable on `(0,∞)`: the bracket factor is bounded
by `C/2 + s + 1`, so `|f'| ≤ (C/2+s+1)·saddleDensity`, which is integrable. -/
lemma integrableOn_saddleDensity_shift_deriv {s : ℝ} (hs : 0 < s) :
    IntegrableOn
      (fun x : ℝ => saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1)))
      (Set.Ioi (0 : ℝ)) := by
  have hCpos : 0 < C := C_pos
  have hg : IntegrableOn (fun x : ℝ => (C / 2 + s + 1) * saddleDensity s (x + 1)) (Set.Ioi 0) :=
    (integrableOn_saddleDensity_shift hs).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    unfold saddleDensity
    fun_prop
  refine Integrable.mono' hg hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  have hx0 : 0 < x := hx
  have hden : (0 : ℝ) < x + 1 := by linarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (x + 1) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ x + 1 by linarith)
    rwa [Real.sqrt_one] at h
  have hsd_nonneg : 0 ≤ saddleDensity s (x + 1) := by
    unfold saddleDensity; exact div_nonneg (Real.exp_pos _).le hden.le
  have hfac : |C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1)| ≤ C / 2 + s + 1 := by
    have hsp : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr hden
    have h1 : C / (2 * Real.sqrt (x + 1)) ≤ C / 2 := by
      rw [div_mul_eq_div_div]
      exact div_le_self (div_nonneg hCpos.le (by norm_num)) hsq1
    have h1' : 0 ≤ C / (2 * Real.sqrt (x + 1)) := by positivity
    have h2 : 1 / (x + 1) ≤ 1 := by rw [div_le_one hden]; linarith
    have h2' : 0 ≤ 1 / (x + 1) := by positivity
    rw [abs_le]
    constructor <;> nlinarith [hCpos.le, hs.le]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsd_nonneg]
  calc saddleDensity s (x + 1) * |C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1)|
      ≤ saddleDensity s (x + 1) * (C / 2 + s + 1) :=
        mul_le_mul_of_nonneg_left hfac hsd_nonneg
    _ = (C / 2 + s + 1) * saddleDensity s (x + 1) := by ring

/-- Finite-interval `u = v²` substitution: `∫₁^{B²} e^{C√u−su}/u du = ∫₁^B 2e^{Cv−sv²}/v dv`.
The image `[1,B²] ⊂ (0,∞)` dodges the `1/u` singularity, so `integral_comp_mul_deriv'` applies. -/
lemma modelSaddleInterval_substitution {s B : ℝ} (hB : 1 ≤ B) :
    (∫ u in (1 : ℝ)..(B ^ 2), saddleDensity s u)
      = ∫ v in (1 : ℝ)..B, 2 * Real.exp (C * v - s * v ^ 2) / v := by
  have hderiv : ∀ v ∈ Set.uIcc (1 : ℝ) B, HasDerivAt (fun y : ℝ => y ^ 2) (2 * v) v := by
    intro v _; simpa using hasDerivAt_pow 2 v
  have hcont' : ContinuousOn (fun v : ℝ => 2 * v) (Set.uIcc 1 B) :=
    (continuous_const.mul continuous_id).continuousOn
  have hcontg : ContinuousOn (saddleDensity s) ((fun y : ℝ => y ^ 2) '' Set.uIcc 1 B) := by
    refine ContinuousOn.mono (s := Set.Ioi (0 : ℝ)) ?_ ?_
    · unfold saddleDensity
      refine ContinuousOn.div ?_ continuousOn_id ?_
      · exact (by fun_prop : Continuous fun u : ℝ => Real.exp (C * Real.sqrt u - s * u)).continuousOn
      · intro u hu; exact ne_of_gt hu
    · rintro u ⟨v, hv, rfl⟩
      rw [Set.uIcc_of_le hB] at hv
      have hv1 : (1 : ℝ) ≤ v := hv.1
      show (0 : ℝ) < v ^ 2
      nlinarith [hv1]
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hcont' hcontg
  simp only [one_pow] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [Set.uIcc_of_le hB] at hv
  have hv1 : (1 : ℝ) ≤ v := hv.1
  simp only [Function.comp, saddleDensity]
  rw [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ v)]
  field_simp

/-- Saddle complete-the-square: `Cv − sv² = A/s − s(v − C/(2s))²` (uses `C² = 4A`),
exposing the saddle at `v₀ = C/(2s)` with peak value `A/s`. -/
lemma saddle_complete_square {s : ℝ} (hs : 0 < s) (v : ℝ) :
    C * v - s * v ^ 2 = Partitions.A / s - s * (v - C / (2 * s)) ^ 2 := by
  have hA : Partitions.A = C ^ 2 / 4 := by rw [C_sq_eq_four_mul_A]; ring
  rw [hA]
  field_simp
  ring

/-- The `v`-integrand `2e^{Cv−sv²}/v` is integrable on `(1,∞)` (Gaussian domination). -/
lemma integrableOn_vIntegrand {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun v : ℝ => 2 * Real.exp (C * v - s * v ^ 2) / v) (Set.Ioi (1 : ℝ)) := by
  have hCpos : 0 < C := C_pos
  have hgauss : Integrable (fun v : ℝ => Real.exp (-(s / 2) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (half_pos hs)
  have hdom : IntegrableOn
      (fun v : ℝ => 2 * Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2) * v ^ 2)) (Set.Ioi 1) :=
    (hgauss.integrableOn).const_mul _
  have hmeas : AEStronglyMeasurable (fun v : ℝ => 2 * Real.exp (C * v - s * v ^ 2) / v)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    apply Measurable.aestronglyMeasurable; fun_prop
  refine Integrable.mono' hdom hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with v hv
  have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
  have hvpos : 0 < v := by linarith
  have hexp : C * v - s * v ^ 2 ≤ C ^ 2 / (2 * s) - (s / 2) * v ^ 2 := by
    rw [le_sub_iff_add_le, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s)]
    nlinarith [sq_nonneg (s * v - C)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc 2 * Real.exp (C * v - s * v ^ 2) / v
      ≤ 2 * Real.exp (C * v - s * v ^ 2) := div_le_self (by positivity) hv1
    _ ≤ 2 * Real.exp (C ^ 2 / (2 * s) - (s / 2) * v ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
    _ = 2 * Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2) * v ^ 2) := by
        rw [show C ^ 2 / (2 * s) - (s / 2) * v ^ 2 = C ^ 2 / (2 * s) + -(s / 2) * v ^ 2 by ring,
          Real.exp_add]; ring

/-- `saddleDensity s` is integrable on `(1,∞)` (exp domination, no singularity for `u ≥ 1`). -/
lemma integrableOn_saddleDensity_Ioi1 {s : ℝ} (hs : 0 < s) :
    IntegrableOn (saddleDensity s) (Set.Ioi (1 : ℝ)) := by
  have hmeas : AEStronglyMeasurable (saddleDensity s) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    apply Measurable.aestronglyMeasurable; unfold saddleDensity; fun_prop
  have hdom : IntegrableOn
      (fun u : ℝ => Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2) * u)) (Set.Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 (half_pos hs)).const_mul _
  refine Integrable.mono' hdom hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with u hu
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
  have hupos : 0 < u := by linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by rw [saddleDensity]; exact div_nonneg (Real.exp_pos _).le hupos.le)]
  unfold saddleDensity
  calc Real.exp (C * Real.sqrt u - s * u) / u
      ≤ Real.exp (C * Real.sqrt u - s * u) := div_le_self (by positivity) hu1
    _ ≤ Real.exp (C ^ 2 / (2 * s) - (s / 2) * u) :=
        Real.exp_le_exp.mpr (saddle_exponent_bound_real hs (le_of_lt hupos))
    _ = Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2) * u) := by
        rw [show C ^ 2 / (2 * s) - (s / 2) * u = C ^ 2 / (2 * s) + -(s / 2) * u by ring,
          Real.exp_add]

/-- `Ioi`-level `x=y²` substitution: `∫_{Ioi 1} e^{C√u−su}/u = ∫_{Ioi 1} 2e^{Cv−sv²}/v`. -/
lemma modelSaddleIoi_substitution {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Ioi (1 : ℝ), saddleDensity s u)
      = ∫ v in Set.Ioi (1 : ℝ), 2 * Real.exp (C * v - s * v ^ 2) / v := by
  have hb2 : Tendsto (fun B : ℝ => B ^ 2) atTop atTop := by
    simpa [pow_two] using tendsto_id.atTop_mul_atTop₀ tendsto_id
  have hlim1 := intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_saddleDensity_Ioi1 hs) hb2
  have hlim2 := intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_vIntegrand hs)
    (tendsto_id (α := ℝ))
  have heq : ∀ᶠ B : ℝ in atTop,
      (∫ u in (1 : ℝ)..B ^ 2, saddleDensity s u)
        = ∫ v in (1 : ℝ)..B, 2 * Real.exp (C * v - s * v ^ 2) / v := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    exact modelSaddleInterval_substitution hB
  exact tendsto_nhds_unique (hlim1.congr' heq) hlim2

/-- Pull out the peak factor `e^{A/s}` via complete-the-square:
`∫_{Ioi 1} 2e^{Cv−sv²}/v = 2e^{A/s}·∫_{Ioi 1} e^{−s(v−v₀)²}/v`, `v₀ = C/(2s)`. -/
lemma vIntegral_eq_gaussianForm {s : ℝ} (hs : 0 < s) :
    (∫ v in Set.Ioi (1 : ℝ), 2 * Real.exp (C * v - s * v ^ 2) / v)
      = 2 * Real.exp (Partitions.A / s) *
          ∫ v in Set.Ioi (1 : ℝ), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v := by
  have hcongr : Set.EqOn (fun v : ℝ => 2 * Real.exp (C * v - s * v ^ 2) / v)
      (fun v : ℝ => (2 * Real.exp (Partitions.A / s)) *
        (Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)) (Set.Ioi 1) := by
    intro v _
    simp only
    rw [saddle_complete_square hs v,
      show Partitions.A / s - s * (v - C / (2 * s)) ^ 2
        = Partitions.A / s + -s * (v - C / (2 * s)) ^ 2 by ring, Real.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul]

/-- `n ↦ saddleDensity s n` is summable (it is the modelSaddle summand). -/
lemma summable_saddleDensity_nat {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => saddleDensity s (n : ℝ)) :=
  (summable_modelSaddleTerm hs).congr (fun n => by rw [saddleDensity])

/-- `modelSaddle s = ∑'_n saddleDensity s n`. -/
lemma modelSaddle_eq_tsum {s : ℝ} :
    modelSaddle s = ∑' n : ℕ, saddleDensity s (n : ℝ) :=
  tsum_congr (fun n => by rw [saddleDensity])

/-- The two-term split: `modelSaddle s = saddleDensity s 1 + ∑'_i saddleDensity s (i+2)`
(`saddleDensity s 0 = 0`). -/
lemma modelSaddle_two_term_split {s : ℝ} (hs : 0 < s) :
    modelSaddle s = saddleDensity s 1 + ∑' i : ℕ, saddleDensity s ((i : ℝ) + 2) := by
  rw [modelSaddle_eq_tsum]
  have hsum := (summable_saddleDensity_nat hs).sum_add_tsum_nat_add 2
  rw [← hsum]
  have hr : (∑ i ∈ Finset.range 2, saddleDensity s (i : ℝ)) = saddleDensity s 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : saddleDensity s ((0 : ℕ) : ℝ) = 0 := by simp [saddleDensity]
    rw [h0]; norm_num
  rw [hr]
  congr 1
  refine tsum_congr (fun i => ?_)
  congr 1; push_cast; ring

/-- The riemann-sum term (mesh 1, `f = saddleDensity s (·+1)`) equals
`modelSaddle s − saddleDensity s 1`. -/
lemma riemann_term_eq {s : ℝ} (hs : 0 < s) :
    (∑' k : ℕ, if k = 0 then (0 : ℝ) else saddleDensity s ((k : ℝ) + 1))
      = modelSaddle s - saddleDensity s 1 := by
  set r : ℕ → ℝ := fun k => if k = 0 then (0 : ℝ) else saddleDensity s ((k : ℝ) + 1) with hr
  -- r is summable: it agrees with the (summable) shift away from 0
  have hshift2 : Summable (fun i : ℕ => saddleDensity s ((i : ℝ) + 2)) := by
    have := (summable_saddleDensity_nat hs)
    rw [← summable_nat_add_iff 2] at this
    exact this.congr (fun i => by push_cast; ring_nf)
  have hrsucc : Summable (fun k : ℕ => r (k + 1)) := by
    refine hshift2.congr (fun i => ?_)
    simp only [hr]
    rw [if_neg (show i + 1 ≠ 0 by omega)]
    congr 1; push_cast; ring
  have hrsumm : Summable r := (summable_nat_add_iff 1).mp hrsucc
  have hsplit := hrsumm.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at hsplit
  have hr0 : r 0 = 0 := by simp [hr]
  rw [hr0, zero_add] at hsplit
  rw [← hsplit, modelSaddle_two_term_split hs, add_sub_cancel_left]
  refine tsum_congr (fun i => ?_)
  simp only [hr]
  rw [if_neg (show i + 1 ≠ 0 by omega)]
  congr 1; push_cast; ring

/-- Sum↔integral comparison (riemann, mesh 1): the discrete `modelSaddle` differs from the
shifted continuous integral by at most `∫|f'| + e^{C√3}`. -/
lemma modelSaddle_sub_integral_bound {s : ℝ} (hs : 0 < s) :
    |modelSaddle s - saddleDensity s 1 - ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)|
      ≤ (∫ x in Set.Ioi (0 : ℝ),
            |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
        + Real.exp (C * Real.sqrt 3) := by
  have hCpos : 0 < C := C_pos
  have hbdd : ∀ x : ℝ, 0 < x → x ≤ 2 → |saddleDensity s (x + 1)| ≤ Real.exp (C * Real.sqrt 3) := by
    intro x hx0 hx2
    have hden : (0 : ℝ) < x + 1 := by linarith
    have hx1 : (1 : ℝ) ≤ x + 1 := by linarith
    rw [saddleDensity, abs_of_nonneg (div_nonneg (Real.exp_pos _).le hden.le)]
    calc Real.exp (C * Real.sqrt (x + 1) - s * (x + 1)) / (x + 1)
        ≤ Real.exp (C * Real.sqrt (x + 1) - s * (x + 1)) := div_le_self (by positivity) hx1
      _ ≤ Real.exp (C * Real.sqrt (x + 1)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg hs.le hden.le]
      _ ≤ Real.exp (C * Real.sqrt 3) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hCpos.le
  have hmain := riemann_sum_Ioi_sub_integral_bound
    (f := fun x => saddleDensity s (x + 1))
    (f' := fun x => saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1)))
    (M := Real.exp (C * Real.sqrt 3)) (η := 2) (by norm_num) (by positivity)
    (fun x hx => saddleDensity_shift_hasDerivAt (by linarith))
    (integrableOn_saddleDensity_shift_deriv hs)
    (integrableOn_saddleDensity_shift hs)
    hbdd 1 (by norm_num) (by norm_num)
  simp only [one_div, inv_one, one_mul] at hmain
  rw [riemann_term_eq hs] at hmain
  exact hmain

/-- Translation: `∫_{Ioi 0} saddleDensity s (x+1) = ∫_{Ioi 1} saddleDensity s`. -/
lemma saddleDensity_shift_integral_eq_Ioi1 {s : ℝ} (hs : 0 < s) :
    (∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1))
      = ∫ x in Set.Ioi (1 : ℝ), saddleDensity s x := by
  have hb : Tendsto (fun B : ℝ => B + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hlimL := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_saddleDensity_shift hs) (tendsto_id (α := ℝ))
  have hlimR := intervalIntegral_tendsto_integral_Ioi 1
    (integrableOn_saddleDensity_Ioi1 hs) hb
  have heq : ∀ᶠ B : ℝ in atTop,
      (∫ x in (0 : ℝ)..B, saddleDensity s (x + 1))
        = ∫ x in (1 : ℝ)..(B + 1), saddleDensity s x := by
    filter_upwards with B
    rw [intervalIntegral.integral_comp_add_right (saddleDensity s) 1]
    norm_num
  exact tendsto_nhds_unique (hlimL.congr' heq) hlimR

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Moving-limit Gaussian DCT core (HR brick 4)

The transformed Gaussian kernel `e^{-u²}/(1+βu)` (with `β = 2√s/C → 0`), restricted to
the moving domain `u > α(s) = -C/(4√s) → -∞`, converges in `L¹`-dominated fashion to
`e^{-u²}`, hence its integral → `√π` (`integral_gaussian`). This is the analytic heart
of `∫_{Ioi 1} e^{-s(v-v₀)²}/v ~ (2√π/C)√s`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval

noncomputable section

/-- `∫_ℝ e^{-u²} = √π` (real wrapper around `integral_gaussian`). -/
lemma integral_exp_neg_sq : (∫ u : ℝ, Real.exp (-(u ^ 2))) = Real.sqrt Real.pi := by
  have h := integral_gaussian 1
  simp only [neg_one_mul, div_one] at h
  simpa using h

/-- Moving lower limit `α(s) = -C/(4√s) → -∞` as `s → 0⁺`. -/
def gaussianTailAlpha (s : ℝ) : ℝ := -C / (4 * Real.sqrt s)

/-- Shrinking distortion `β(s) = 2√s/C → 0`. -/
def gaussianTailBeta (s : ℝ) : ℝ := 2 * Real.sqrt s / C

/-- The transformed kernel `e^{-u²}/(1+βu)` cut off below `α(s)`. -/
noncomputable def gaussianTailKernel (s u : ℝ) : ℝ :=
  Set.indicator (Set.Ioi (gaussianTailAlpha s))
    (fun u : ℝ => Real.exp (-(u ^ 2)) / (1 + gaussianTailBeta s * u)) u

/-- `√s → 0⁺` within `𝓝[>] 0`. -/
lemma sqrt_tendsto_nhdsGT_zero :
    Tendsto (fun s : ℝ => Real.sqrt s) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have h0 : Tendsto (fun s : ℝ => Real.sqrt s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rwa [Real.sqrt_zero] at this
  rw [tendsto_nhdsWithin_iff]
  refine ⟨h0, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact Real.sqrt_pos.mpr hs

lemma gaussianTailAlpha_tendsto_atBot :
    Tendsto gaussianTailAlpha (𝓝[>] (0 : ℝ)) atBot := by
  have hCpos : 0 < C := C_pos
  unfold gaussianTailAlpha
  have hinv : Tendsto (fun s : ℝ => 1 / Real.sqrt s) (𝓝[>] (0 : ℝ)) atTop := by
    simpa [one_div] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp sqrt_tendsto_nhdsGT_zero
  have hmul : Tendsto (fun s : ℝ => -(C / 4) * (1 / Real.sqrt s)) (𝓝[>] (0 : ℝ)) atBot :=
    (tendsto_const_mul_atBot_of_neg (by linarith : -(C / 4) < 0)).mpr hinv
  refine hmul.congr (fun s => ?_)
  rw [div_eq_mul_inv]; ring

lemma gaussianTailBeta_tendsto_zero :
    Tendsto gaussianTailBeta (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsqrt0 : Tendsto (fun s : ℝ => Real.sqrt s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    sqrt_tendsto_nhdsGT_zero.mono_right nhdsWithin_le_nhds
  have h := hsqrt0.const_mul (2 / C)
  rw [mul_zero] at h
  exact h.congr (fun s => by unfold gaussianTailBeta; ring)

/-- Pointwise: for fixed `u`, the kernel → `e^{-u²}` (`α(s) < u` eventually, denominator → 1). -/
lemma gaussianTailKernel_pointwise :
    ∀ᵐ u : ℝ, Tendsto (fun s : ℝ => gaussianTailKernel s u)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (-(u ^ 2)))) := by
  refine ae_of_all _ (fun u => ?_)
  have hα_event : ∀ᶠ s in 𝓝[>] (0 : ℝ), gaussianTailAlpha s < u := by
    filter_upwards [tendsto_atBot.mp gaussianTailAlpha_tendsto_atBot (u - 1)] with s hs
    linarith
  have hden : Tendsto (fun s : ℝ => 1 + gaussianTailBeta s * u) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.add (gaussianTailBeta_tendsto_zero.mul_const u)
  have hquot : Tendsto (fun s : ℝ => Real.exp (-(u ^ 2)) / (1 + gaussianTailBeta s * u))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (-(u ^ 2)) / 1)) :=
    tendsto_const_nhds.div hden (by norm_num)
  rw [div_one] at hquot
  refine hquot.congr' ?_
  filter_upwards [hα_event] with s hs
  simp [gaussianTailKernel, hs]

/-- Dominating function `2e^{-u²}` (denominator `≥ 1/2` on the cut domain). -/
lemma gaussianTailKernel_dom :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᵐ u : ℝ,
      ‖gaussianTailKernel s u‖ ≤ 2 * Real.exp (-(u ^ 2)) := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hCpos : 0 < C := C_pos
  refine ae_of_all _ (fun u => ?_)
  by_cases hu : gaussianTailAlpha s < u
  · have hden_lb : (1 : ℝ) / 2 ≤ 1 + gaussianTailBeta s * u := by
      have hmul := mul_lt_mul_of_pos_left hu (show (0 : ℝ) < 2 * Real.sqrt s / C by positivity)
      have hleft : (2 * Real.sqrt s / C) * gaussianTailAlpha s = -(1 / 2 : ℝ) := by
        unfold gaussianTailAlpha
        field_simp
        ring
      rw [hleft] at hmul
      unfold gaussianTailBeta
      nlinarith [hmul]
    have hden_pos : 0 < 1 + gaussianTailBeta s * u := by linarith
    simp only [gaussianTailKernel, Set.indicator_of_mem (Set.mem_Ioi.mpr hu), Real.norm_eq_abs]
    rw [abs_div, abs_of_pos hden_pos, abs_of_pos (Real.exp_pos _)]
    rw [div_le_iff₀ hden_pos]
    nlinarith [Real.exp_pos (-(u ^ 2)), hden_lb]
  · have hzero : gaussianTailKernel s u = 0 := by
      simp only [gaussianTailKernel]
      exact Set.indicator_of_notMem (by rw [Set.mem_Ioi]; exact hu) _
    rw [hzero, norm_zero]
    positivity

lemma integrable_gaussian_dom : Integrable (fun u : ℝ => 2 * Real.exp (-(u ^ 2))) := by
  have hbase : Integrable (fun u : ℝ => Real.exp (-(1 : ℝ) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  exact (hbase.const_mul 2).congr (by filter_upwards with u; simp [neg_one_mul])

/-- The cut Gaussian kernel integral → `√π` (DCT, moving lower limit). -/
lemma gaussianTailKernel_integral_tendsto :
    Tendsto (fun s : ℝ => ∫ u : ℝ, gaussianTailKernel s u)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt Real.pi)) := by
  have Hmeas : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (gaussianTailKernel s) volume := by
    refine Eventually.of_forall (fun s => ?_)
    unfold gaussianTailKernel
    refine (AEStronglyMeasurable.indicator ?_ measurableSet_Ioi)
    exact Measurable.aestronglyMeasurable (by measurability)
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (bound := fun u : ℝ => 2 * Real.exp (-(u ^ 2)))
    Hmeas gaussianTailKernel_dom integrable_gaussian_dom gaussianTailKernel_pointwise
  rwa [integral_exp_neg_sq] at hlim

/-- Saddle cutoff `q(s) = C/(4s) = v₀/2`. -/
def gaussianTailCut (s : ℝ) : ℝ := C / (4 * s)

/-- `√s·(c/(k·s)) = c/(k·√s)` (one `√s` cancels). -/
lemma sqrt_mul_div_self {s k : ℝ} (hs : 0 < s) (hk : 0 < k) (c : ℝ) :
    Real.sqrt s * (c / (k * s)) = c / (k * Real.sqrt s) := by
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hkne : k ≠ 0 := ne_of_gt hk
  have hsne : s ≠ 0 := ne_of_gt hs
  have hsqne : Real.sqrt s ≠ 0 := ne_of_gt hsqrtpos
  field_simp
  linear_combination c * hss

/-- Key denominator identity: `C/(2√s) + √s·(v − C/(2s)) = √s·v`. -/
lemma gaussianTail_denom_id {s : ℝ} (hs : 0 < s) (v : ℝ) :
    C / (2 * Real.sqrt s) + Real.sqrt s * (v - C / (2 * s)) = Real.sqrt s * v := by
  rw [mul_sub, sqrt_mul_div_self (k := 2) hs (by norm_num) C]; ring

/-- Finite-interval affine substitution `u = √s(v − v₀)` for the cut Gaussian:
`∫_{cut}^B e^{−s(v−v₀)²}/v = ∫_{α}^{√s(B−v₀)} e^{−u²}/(C/(2√s)+u)`. -/
lemma gaussianTail_affine_interval {s B : ℝ} (hs : 0 < s)
    (hcutB : gaussianTailCut s ≤ B) :
    (∫ v in gaussianTailCut s..B, Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      = ∫ u in gaussianTailAlpha s..(Real.sqrt s * (B - C / (2 * s))),
          Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u) := by
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hCpos : 0 < C := C_pos
  have hcutpos : 0 < gaussianTailCut s := by
    rw [gaussianTailCut]; exact div_pos hCpos (by positivity)
  set f : ℝ → ℝ := fun v => Real.sqrt s * (v - C / (2 * s)) with hf
  set g : ℝ → ℝ := fun u => Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u) with hg
  have hderiv : ∀ v ∈ Set.uIcc (gaussianTailCut s) B, HasDerivAt f (Real.sqrt s) v := by
    intro v _
    simpa using ((hasDerivAt_id v).sub_const (C / (2 * s))).const_mul (Real.sqrt s)
  have hcont' : ContinuousOn (fun _ : ℝ => Real.sqrt s) (Set.uIcc (gaussianTailCut s) B) :=
    continuousOn_const
  have hcontg : ContinuousOn g (f '' Set.uIcc (gaussianTailCut s) B) := by
    refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn (by fun_prop)) ?_
    rintro u ⟨v, hv, rfl⟩
    rw [Set.uIcc_of_le hcutB] at hv
    have hvpos : 0 < v := lt_of_lt_of_le hcutpos hv.1
    rw [hf, gaussianTail_denom_id hs v]
    exact ne_of_gt (mul_pos hsqrtpos hvpos)
  have hsqrtne : Real.sqrt s ≠ 0 := ne_of_gt hsqrtpos
  have hfcut : f (gaussianTailCut s) = gaussianTailAlpha s := by
    simp only [hf, gaussianTailCut, gaussianTailAlpha]
    rw [mul_sub, sqrt_mul_div_self (k := 4) hs (by norm_num) C,
      sqrt_mul_div_self (k := 2) hs (by norm_num) C]
    field_simp
    ring
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hcont' hcontg
  rw [hfcut] at hsub
  rw [← hsub]
  refine (intervalIntegral.integral_congr ?_)
  intro v hv
  rw [Set.uIcc_of_le hcutB] at hv
  have hvpos : 0 < v := lt_of_lt_of_le hcutpos hv.1
  have hvne : v ≠ 0 := ne_of_gt hvpos
  have hsne : Real.sqrt s ≠ 0 := ne_of_gt hsqrtpos
  simp only [Function.comp, hf, hg]
  rw [show -(Real.sqrt s * (v - C / (2 * s))) ^ 2 = -s * (v - C / (2 * s)) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hs.le]; ring, gaussianTail_denom_id hs v]
  field_simp

lemma gaussianTailCut_pos {s : ℝ} (hs : 0 < s) : 0 < gaussianTailCut s := by
  rw [gaussianTailCut]; exact div_pos C_pos (by positivity)

/-- Shifted Gaussian over `v` is integrable on all of `ℝ`. -/
lemma integrable_gaussShift {s : ℝ} (hs : 0 < s) :
    Integrable (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq hs).comp_sub_right (C / (2 * s))
  simpa using h

/-- `e^{-s(v-v₀)²}/v` integrable on `(cut,∞)` (dominated by `(1/cut)·gauss`). -/
lemma integrableOn_gaussShift_div {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      (Set.Ioi (gaussianTailCut s)) := by
  have hcutpos : 0 < gaussianTailCut s := gaussianTailCut_pos hs
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      (volume.restrict (Set.Ioi (gaussianTailCut s))) := by
    apply Measurable.aestronglyMeasurable; fun_prop
  refine Integrable.mono'
    ((integrable_gaussShift hs).integrableOn.const_mul (1 / gaussianTailCut s)) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with v hv
  have hvcut : gaussianTailCut s < v := hv
  have hvpos : 0 < v := lt_trans hcutpos hvcut
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.exp (-s * (v - C / (2 * s)) ^ 2) / v
      ≤ Real.exp (-s * (v - C / (2 * s)) ^ 2) / gaussianTailCut s := by
        gcongr
    _ = 1 / gaussianTailCut s * Real.exp (-s * (v - C / (2 * s)) ^ 2) := by
        rw [div_eq_inv_mul, one_div]

/-- `e^{-u²}/(C/(2√s)+u)` integrable on `(α,∞)` (denominator `≥ C/(4√s)`). -/
lemma integrableOn_uKernel {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u))
      (Set.Ioi (gaussianTailAlpha s)) := by
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hgauss : Integrable (fun u : ℝ => Real.exp (-(u ^ 2))) := by
    have := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    simpa [neg_one_mul] using this
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u))
      (volume.restrict (Set.Ioi (gaussianTailAlpha s))) := by
    apply Measurable.aestronglyMeasurable; fun_prop
  refine Integrable.mono'
    (hgauss.integrableOn.const_mul (4 * Real.sqrt s / C)) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with u hu
  have hu_lb : gaussianTailAlpha s < u := hu
  have hkey : C / (2 * Real.sqrt s) - C / (4 * Real.sqrt s) = C / (4 * Real.sqrt s) := by
    field_simp; ring
  have hden_lb : C / (4 * Real.sqrt s) ≤ C / (2 * Real.sqrt s) + u := by
    unfold gaussianTailAlpha at hu_lb
    have h2 : -C / (4 * Real.sqrt s) = -(C / (4 * Real.sqrt s)) := by ring
    rw [h2] at hu_lb
    linarith [hu_lb, hkey]
  have hden_pos : 0 < C / (2 * Real.sqrt s) + u :=
    lt_of_lt_of_le (by positivity) hden_lb
  have hge : (1 : ℝ) ≤ (4 * Real.sqrt s / C) * (C / (2 * Real.sqrt s) + u) := by
    have hone : (4 * Real.sqrt s / C) * (C / (4 * Real.sqrt s)) = 1 := by field_simp
    calc (1 : ℝ) = (4 * Real.sqrt s / C) * (C / (4 * Real.sqrt s)) := hone.symm
      _ ≤ (4 * Real.sqrt s / C) * (C / (2 * Real.sqrt s) + u) :=
        mul_le_mul_of_nonneg_left hden_lb (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hden_pos]
  calc Real.exp (-(u ^ 2)) = Real.exp (-(u ^ 2)) * 1 := (mul_one _).symm
    _ ≤ Real.exp (-(u ^ 2)) * ((4 * Real.sqrt s / C) * (C / (2 * Real.sqrt s) + u)) :=
        mul_le_mul_of_nonneg_left hge (Real.exp_pos _).le
    _ = 4 * Real.sqrt s / C * Real.exp (-(u ^ 2)) * (C / (2 * Real.sqrt s) + u) := by ring

/-- `∫_{Ioi cut} e^{-s(v-v₀)²}/v = (2√s/C)·∫_ℝ gaussianTailKernel s` (affine subst + B→∞). -/
lemma modelGaussCut_eq {s : ℝ} (hs : 0 < s) :
    (∫ v in Set.Ioi (gaussianTailCut s), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      = (2 * Real.sqrt s / C) * ∫ u : ℝ, gaussianTailKernel s u := by
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  -- step 1: ∫_{Ioi cut} = ∫_{Ioi α} e^{-u²}/(C/2√s+u)
  have hb : Tendsto (fun B : ℝ => Real.sqrt s * (B - C / (2 * s))) atTop atTop := by
    have h1 : Tendsto (fun B : ℝ => B - C / (2 * s)) atTop atTop :=
      tendsto_atTop_add_const_right atTop _ tendsto_id
    exact Tendsto.const_mul_atTop hsqrtpos h1
  have hlimL := intervalIntegral_tendsto_integral_Ioi (gaussianTailCut s)
    (integrableOn_gaussShift_div hs) (tendsto_id (α := ℝ))
  have hlimR := intervalIntegral_tendsto_integral_Ioi (gaussianTailAlpha s)
    (integrableOn_uKernel hs) hb
  have heq : ∀ᶠ B : ℝ in atTop,
      (∫ v in gaussianTailCut s..B, Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
        = ∫ u in gaussianTailAlpha s..(Real.sqrt s * (B - C / (2 * s))),
            Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u) := by
    filter_upwards [eventually_ge_atTop (gaussianTailCut s)] with B hB
    exact gaussianTail_affine_interval hs hB
  have step1 :
      (∫ v in Set.Ioi (gaussianTailCut s), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
        = ∫ u in Set.Ioi (gaussianTailAlpha s),
            Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u) :=
    tendsto_nhds_unique (hlimL.congr' heq) hlimR
  rw [step1]
  -- step 2: kernel integral = ∫_{Ioi α} e^{-u²}/(1+βu); pull (2√s/C)
  have hkernel_int : (∫ u, gaussianTailKernel s u)
      = ∫ u in Set.Ioi (gaussianTailAlpha s),
          Real.exp (-(u ^ 2)) / (1 + gaussianTailBeta s * u) := by
    simp only [gaussianTailKernel]
    exact integral_indicator measurableSet_Ioi
  rw [hkernel_int, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu_lb : gaussianTailAlpha s < u := hu
  have hbpos : 0 < 1 + gaussianTailBeta s * u := by
    have hmono : gaussianTailBeta s * gaussianTailAlpha s < gaussianTailBeta s * u :=
      mul_lt_mul_of_pos_left hu_lb (by unfold gaussianTailBeta; positivity)
    have hval : gaussianTailBeta s * gaussianTailAlpha s = -(1 / 2 : ℝ) := by
      unfold gaussianTailBeta gaussianTailAlpha; rw [neg_div, mul_neg]; field_simp; ring
    rw [hval] at hmono; linarith
  have hdenpos : 0 < C / (2 * Real.sqrt s) + u := by
    have h2 : gaussianTailAlpha s = -(C / (4 * Real.sqrt s)) := by
      unfold gaussianTailAlpha; ring
    have hval2 : C / (2 * Real.sqrt s) + gaussianTailAlpha s = C / (4 * Real.sqrt s) := by
      rw [h2, ← sub_eq_add_neg]; field_simp; ring
    have hlt : C / (2 * Real.sqrt s) + gaussianTailAlpha s < C / (2 * Real.sqrt s) + u := by
      linarith
    rw [hval2] at hlt
    exact lt_trans (by positivity) hlt
  have hbne : (1 + gaussianTailBeta s * u) ≠ 0 := ne_of_gt hbpos
  have hdne : (C / (2 * Real.sqrt s) + u) ≠ 0 := ne_of_gt hdenpos
  unfold gaussianTailBeta
  field_simp

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# Gaussian tail asymptotic (HR brick 4): `∫_{Ioi 1} e^{-s(v-v₀)²}/v ~ (2√π/C)√s`

Splits at the saddle cutoff `cut = C/(4s)`: the right part gives the main
`(2√s/C)·√π` (via `modelGaussCut_eq` + DCT); the left strip is exponentially negligible.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval

noncomputable section

/-- The full Gaussian tail integral after completing the square. -/
noncomputable def gaussianTailFull (s : ℝ) : ℝ :=
  ∫ v in Set.Ioi (1 : ℝ), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v

/-- Right (central) part: ratio → 1. -/
lemma gaussianTail_cut_ratio_tendsto :
    Tendsto
      (fun s : ℝ =>
        (∫ v in Set.Ioi (gaussianTailCut s), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hK : Tendsto (fun s : ℝ => (∫ u : ℝ, gaussianTailKernel s u) / Real.sqrt Real.pi)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
    have h := gaussianTailKernel_integral_tendsto.div_const (Real.sqrt Real.pi)
    simpa [hsqrtpi] using h
  refine hK.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  rw [modelGaussCut_eq hspos]
  field_simp

/-- `(s⁻¹)^{3/2} = (s·√s)⁻¹`. -/
lemma inv_rpow_three_halves {s : ℝ} (hs : 0 < s) :
    (s⁻¹) ^ ((3 : ℝ) / 2) = (s * Real.sqrt s)⁻¹ := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
    ← Real.sqrt_eq_rpow, Real.sqrt_inv, ← mul_inv]

/-- The exponential-decay bound function `(C/4s)·e^{-(C²/16)/s}/((2√π/C)√s) → 0`. -/
lemma gaussianTail_strip_bound_tendsto_zero :
    Tendsto
      (fun s : ℝ =>
        (C / (4 * s)) * Real.exp (-(C ^ 2 / 16) * s⁻¹) / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hCpos : 0 < C := C_pos
  have hc : 0 < C ^ 2 / 16 := by positivity
  have hcomp : Tendsto
      (fun σ : ℝ => σ ^ ((3 : ℝ) / 2) * Real.exp (-(C ^ 2 / 16) * σ)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / 2) (C ^ 2 / 16) hc
  have hmul := (hcomp.comp tendsto_inv_nhdsGT_zero).const_mul (C ^ 2 / (8 * Real.sqrt Real.pi))
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  simp only [Function.comp_apply]
  rw [inv_rpow_three_halves hspos]
  field_simp
  ring

/-- `cut s = C/(4s) → ∞`, so eventually `1 ≤ cut s`. -/
lemma eventually_one_le_cut : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 1 ≤ gaussianTailCut s := by
  have hto : Tendsto gaussianTailCut (𝓝[>] (0 : ℝ)) atTop := by
    unfold gaussianTailCut
    have hinv : Tendsto (fun s : ℝ => s⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
    have h2 : Tendsto (fun s : ℝ => C / 4 * s⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      Tendsto.const_mul_atTop (div_pos C_pos (by norm_num)) hinv
    refine h2.congr (fun s => ?_); rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  exact hto.eventually_ge_atTop 1

/-- `e^{-s(v-v₀)²}/v` integrable on `(1,∞)` (dominated by the shifted Gaussian). -/
lemma integrableOn_gaussShift_div_Ioi1 {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v) (Set.Ioi (1 : ℝ)) := by
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    apply Measurable.aestronglyMeasurable; fun_prop
  refine (integrable_gaussShift hs).integrableOn.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with v hv
  have hv1 : (1 : ℝ) < v := hv
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
  nlinarith [Real.exp_pos (-s * (v - C / (2 * s)) ^ 2), hv1]

/-- Left strip ratio → 0. -/
lemma gaussianTail_left_ratio_tendsto_zero :
    Tendsto
      (fun s : ℝ =>
        (∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hCpos : 0 < C := C_pos
  refine squeeze_zero' ?_ ?_ gaussianTail_strip_bound_tendsto_zero
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
    have hi : 0 ≤ ∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s),
        Real.exp (-s * (v - C / (2 * s)) ^ 2) / v :=
      setIntegral_nonneg measurableSet_Ioc (fun v hv => by
        have : (0 : ℝ) < v := lt_trans one_pos hv.1; positivity)
    have hdenpos : (0 : ℝ) < (2 * Real.sqrt Real.pi / C) * Real.sqrt s := by positivity
    exact div_nonneg hi hdenpos.le
  · filter_upwards [self_mem_nhdsWithin, eventually_one_le_cut] with s hs hcutge
    have hspos : 0 < s := hs
    have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
    have hdenpos : (0 : ℝ) < (2 * Real.sqrt Real.pi / C) * Real.sqrt s := by positivity
    have hpt : ∀ v ∈ Set.Ioc (1 : ℝ) (gaussianTailCut s),
        ‖Real.exp (-s * (v - C / (2 * s)) ^ 2) / v‖ ≤ Real.exp (-(C ^ 2 / 16) * s⁻¹) := by
      intro v hv
      have hv1 : (1 : ℝ) < v := hv.1
      have hvpos : 0 < v := lt_trans one_pos hv1
      have hvle : v ≤ C / (4 * s) := by rw [gaussianTailCut] at *; exact hv.2
      have hkey : (C / (4 * s)) ^ 2 ≤ (v - C / (2 * s)) ^ 2 := by
        have h1 : v - C / (2 * s) ≤ -(C / (4 * s)) := by
          have hcc : C / (4 * s) = C / (2 * s) - C / (4 * s) := by field_simp; ring
          nlinarith [hvle, hcc]
        nlinarith [h1, sq_nonneg (v - C / (2 * s))]
      have hcl : C ^ 2 ≤ 16 * s ^ 2 * (v - C / (2 * s)) ^ 2 := by
        have he : (C / (4 * s)) ^ 2 = C ^ 2 / (16 * s ^ 2) := by ring
        rw [he, div_le_iff₀ (by positivity : (0 : ℝ) < 16 * s ^ 2)] at hkey
        linarith [hkey]
      have hexpbound : Real.exp (-s * (v - C / (2 * s)) ^ 2) ≤ Real.exp (-(C ^ 2 / 16) * s⁻¹) := by
        apply Real.exp_le_exp.mpr
        rw [neg_mul, neg_mul, neg_le_neg_iff]
        have hsc : s * s⁻¹ = 1 := mul_inv_cancel₀ hspos.ne'
        nlinarith [hcl, hsc, hspos]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc Real.exp (-s * (v - C / (2 * s)) ^ 2) / v
          ≤ Real.exp (-s * (v - C / (2 * s)) ^ 2) / 1 := by gcongr
        _ = Real.exp (-s * (v - C / (2 * s)) ^ 2) := by rw [div_one]
        _ ≤ Real.exp (-(C ^ 2 / 16) * s⁻¹) := hexpbound
    have hbound := norm_setIntegral_le_of_norm_le_const
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) hpt
    rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc (fun v hv => by
      have : (0 : ℝ) < v := lt_trans one_pos hv.1; positivity))] at hbound
    have hμ : volume.real (Set.Ioc (1 : ℝ) (gaussianTailCut s)) ≤ C / (4 * s) := by
      rw [volume_real_Ioc, max_eq_left (by linarith [hcutge] : (0 : ℝ) ≤ gaussianTailCut s - 1),
        gaussianTailCut]
      linarith
    rw [div_le_iff₀ hdenpos]
    calc ∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v
        ≤ Real.exp (-(C ^ 2 / 16) * s⁻¹) * volume.real (Set.Ioc (1 : ℝ) (gaussianTailCut s)) := hbound
      _ ≤ Real.exp (-(C ^ 2 / 16) * s⁻¹) * (C / (4 * s)) :=
          mul_le_mul_of_nonneg_left hμ (Real.exp_pos _).le
      _ = (C / (4 * s)) * Real.exp (-(C ^ 2 / 16) * s⁻¹)
            / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s)
            * ((2 * Real.sqrt Real.pi / C) * Real.sqrt s) := by field_simp

/-- **Gaussian tail asymptotic.** `∫_{Ioi 1} e^{-s(v-v₀)²}/v ~ (2√π/C)√s`. -/
lemma gaussianTail_asymp :
    Tendsto (fun s : ℝ => gaussianTailFull s / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hsum := gaussianTail_left_ratio_tendsto_zero.add gaussianTail_cut_ratio_tendsto
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_one_le_cut] with s hs hcutge
  have hspos : 0 < s := hs
  have hint1 := integrableOn_gaussShift_div_Ioi1 hspos
  have hIoc : IntegrableOn (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      (Set.Ioc (1 : ℝ) (gaussianTailCut s)) := hint1.mono_set (fun v hv => hv.1)
  have hIoi : IntegrableOn (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      (Set.Ioi (gaussianTailCut s)) := hint1.mono_set (fun v hv => lt_of_le_of_lt hcutge hv)
  have hdisj : Disjoint (Set.Ioc (1 : ℝ) (gaussianTailCut s)) (Set.Ioi (gaussianTailCut s)) := by
    refine Set.disjoint_left.mpr (fun v hv1 hv2 => ?_)
    exact absurd (Set.mem_Ioi.mp hv2) (not_lt.mpr hv1.2)
  have hunion := setIntegral_union hdisj measurableSet_Ioi hIoc hIoi
  rw [Set.Ioc_union_Ioi_eq_Ioi hcutge] at hunion
  rw [← add_div]
  unfold gaussianTailFull
  rw [hunion]

end
end AnalyticCombinatorics.Ch8.Partitions
end

section
/-!
# HR constant final assembly (brick 4 ratio → log → discharge → `a = 1/(4√3)`)

`modelSaddle s ~ (4√π/C)·√s·e^{A/s}` (= `mainScale`), assembled from the riemann
comparison + main term (`gaussianTail_asymp`) + the o()-error `hO`; gives
`modelSaddle_log_asymp` and `modelSaddle_tendsto_atTop`, which discharge bricks 3,4,5
into `a = 1/(4√3)`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval

noncomputable section

/-- The saddle main scale `(4√π/C)·√s·e^{A/s}`. -/
noncomputable def mainScale (s : ℝ) : ℝ :=
  (4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (Partitions.A / s)

lemma mainScale_pos {s : ℝ} (hs : 0 < s) : 0 < mainScale s := by
  have hCpos : 0 < C := C_pos
  unfold mainScale; positivity

/-- `mainScale → ∞` as `s → 0⁺` (lower-bounded by `const·s^{-1/2}`). -/
lemma mainScale_tendsto_atTop : Tendsto mainScale (𝓝[>] (0 : ℝ)) atTop := by
  have hCpos : 0 < C := C_pos
  have hApos : 0 < Partitions.A := Partitions.A_pos
  -- bound: mainScale s ≥ (4√π·A/C)·s⁻¹^{1/2} = (4√π·A/C)/√s
  have hlow : Tendsto (fun s : ℝ => (4 * Real.sqrt Real.pi * Partitions.A / C) * (Real.sqrt s)⁻¹)
      (𝓝[>] (0 : ℝ)) atTop := by
    have hinv : Tendsto (fun s : ℝ => (Real.sqrt s)⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp sqrt_tendsto_nhdsGT_zero
    exact Tendsto.const_mul_atTop (by positivity) hinv
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hexp : Partitions.A / s ≤ Real.exp (Partitions.A / s) := by
    have := Real.add_one_le_exp (Partitions.A / s); linarith
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hspos.le
  have hid : (4 * Real.sqrt Real.pi * Partitions.A / C) * (Real.sqrt s)⁻¹
      = (4 * Real.sqrt Real.pi / C) * Real.sqrt s * (Partitions.A / s) := by
    field_simp
    linear_combination -hss
  rw [mainScale, hid]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- `T1`: `(∫_{Ioi 0} sd(·+1)) / mainScale → 1`. -/
lemma shiftIntegral_div_mainScale_tendsto_one :
    Tendsto (fun s : ℝ => (∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) / mainScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  refine gaussianTail_asymp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  have hexpne : Real.exp (Partitions.A / s) ≠ 0 := Real.exp_ne_zero _
  have hfold : (∫ v in Set.Ioi (1 : ℝ), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      = gaussianTailFull s := rfl
  rw [saddleDensity_shift_integral_eq_Ioi1 hs, modelSaddleIoi_substitution hs,
    vIntegral_eq_gaussianForm hs, hfold]
  unfold mainScale
  field_simp
  ring

/-- The o()-error hypothesis: the mesh-1 Riemann error is negligible vs `mainScale`. -/
def RiemannErrorNegligible : Prop :=
  Tendsto
    (fun s : ℝ =>
      ((∫ x in Set.Ioi (0 : ℝ),
          |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
        + Real.exp (C * Real.sqrt 3)) / mainScale s)
    (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- `T2`: `saddleDensity s 1 / mainScale → 0`. -/
lemma sd1_div_mainScale_tendsto_zero :
    Tendsto (fun s : ℝ => saddleDensity s 1 / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hconst : Tendsto (fun s : ℝ => Real.exp C / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_const_nhds (x := Real.exp C)).div_atTop mainScale_tendsto_atTop
  refine squeeze_zero' ?_ ?_ hconst
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have := mainScale_pos hs; rw [saddleDensity]; positivity
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hMSpos : 0 < mainScale s := mainScale_pos hspos
    have hsd1 : saddleDensity s 1 ≤ Real.exp C := by
      rw [saddleDensity, Real.sqrt_one, show C * 1 - s * 1 = C - s by ring, div_one]
      exact Real.exp_le_exp.mpr (by linarith)
    gcongr

/-- **Brick 4 ratio**: `modelSaddle s / mainScale s → 1` (given `hO`). -/
theorem modelSaddle_ratio_asymp (hO : RiemannErrorNegligible) :
    Tendsto (fun s : ℝ => modelSaddle s / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hT1 := shiftIntegral_div_mainScale_tendsto_one
  have hT2 := sd1_div_mainScale_tendsto_zero
  have hCpos : 0 < C := C_pos
  have hO2 : Tendsto
      (fun s : ℝ =>
        ((∫ x in Set.Ioi (0 : ℝ),
            |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
          + Real.exp (C * Real.sqrt 3)) / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 0) := hO
  have hg : Tendsto
      (fun s : ℝ =>
        ((∫ x in Set.Ioi (0 : ℝ),
            |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
          + Real.exp (C * Real.sqrt 3)) / mainScale s + saddleDensity s 1 / mainScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using hO2.add hT2
  have hrest : Tendsto
      (fun s : ℝ =>
        (modelSaddle s - ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) / mainScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hMSpos : 0 < mainScale s := mainScale_pos hspos
    have hsd1 : 0 ≤ saddleDensity s 1 := by rw [saddleDensity]; positivity
    have hb := modelSaddle_sub_integral_bound hspos
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hMSpos, ← add_div]
    gcongr
    calc |modelSaddle s - ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)|
        = |(modelSaddle s - saddleDensity s 1 - ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1))
            + saddleDensity s 1| := by ring_nf
      _ ≤ |modelSaddle s - saddleDensity s 1 - ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)|
          + |saddleDensity s 1| := abs_add_le _ _
      _ ≤ ((∫ x in Set.Ioi (0 : ℝ),
              |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
            + Real.exp (C * Real.sqrt 3)) + saddleDensity s 1 := by
          rw [abs_of_nonneg hsd1]; linarith [hb]
  have hcomb := hrest.add hT1
  rw [zero_add] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hMSpos : 0 < mainScale s := mainScale_pos hs
  rw [← add_div]
  congr 1
  ring

/-- **Brick 4 (atTop)**: `modelSaddle → ∞` as `s → 0⁺`. -/
theorem modelSaddle_tendsto_atTop (hO : RiemannErrorNegligible) :
    Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop := by
  have hratio := modelSaddle_ratio_asymp hO
  have hms := mainScale_tendsto_atTop
  have hhalf : ∀ᶠ s in 𝓝[>] (0 : ℝ), (1 / 2 : ℝ) ≤ modelSaddle s / mainScale s :=
    hratio.eventually (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  refine tendsto_atTop_mono' _ ?_
    (Tendsto.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num) hms)
  filter_upwards [hhalf, self_mem_nhdsWithin] with s hs hspos
  have hMSpos : 0 < mainScale s := mainScale_pos hspos
  have hmeq : modelSaddle s / mainScale s * mainScale s = modelSaddle s := by
    field_simp
  calc (1 / 2 : ℝ) * mainScale s
      ≤ modelSaddle s / mainScale s * mainScale s :=
        mul_le_mul_of_nonneg_right hs hMSpos.le
    _ = modelSaddle s := hmeq

/-- **Brick 4 (log form)**: the `hB4` hypothesis of `erdos_limit_constant_of_asymptotics`. -/
theorem modelSaddle_log_asymp (hO : RiemannErrorNegligible) :
    Tendsto
      (fun t : ℝ =>
        Real.log (modelSaddle t) - Partitions.A / t - (1 / 2 : ℝ) * Real.log t
          - Real.log (4 * Real.sqrt Real.pi / C))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hCpos : 0 < C := C_pos
  have hratio := modelSaddle_ratio_asymp hO
  -- log of the ratio → log 1 = 0
  have hlog : Tendsto (fun s : ℝ => Real.log (modelSaddle s / mainScale s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    simpa [Real.log_one] using this
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hMSpos : 0 < modelSaddle s := modelSaddle_pos hspos
  have hmainpos : 0 < mainScale s := mainScale_pos hspos
  have hsqrtspos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hKpos : 0 < 4 * Real.sqrt Real.pi / C := div_pos (by positivity) hCpos
  rw [Real.log_div (ne_of_gt hMSpos) (ne_of_gt hmainpos)]
  unfold mainScale
  rw [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
    Real.log_mul (ne_of_gt hKpos) (ne_of_gt hsqrtspos),
    Real.log_sqrt hspos.le, Real.log_exp]
  ring

/-- **The Erdős–Hardy–Ramanujan limit constant** is `1/(4√3)`, given the renewal/Tauberian
input `hlim : u n → a` and the negligibility of the mesh-1 Riemann error `hO`. -/
theorem erdos_limit_constant {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto Erdos.u atTop (𝓝 a))
    (hO : RiemannErrorNegligible) :
    a = 1 / (4 * Real.sqrt 3) := by
  have hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop := modelSaddle_tendsto_atTop hO
  have hB3 := partLaplace_log_sub_modelSaddle_tendsto ha hlim hMS_atTop
  have hB4 := modelSaddle_log_asymp hO
  exact erdos_limit_constant_of_asymptotics ha hB3 hB4

end
end AnalyticCombinatorics.Ch8.Partitions
end

/-!
# Discharging the mesh-1 Riemann error (`RiemannErrorNegligible`)

The last hypothesis of `erdos_limit_constant`. We show the bracket-weighted error
integral is `o(mainScale)` by splitting `(0,∞)` at the saddle cutoff `x+1 = (C/4s)²`:

* on the right (`x+1 ≥ (C/4s)²`) the bracket `C/(2√(x+1)) − s − (x+1)⁻¹` is `≤ 2s`;
* on the left (`x+1 ≤ (C/4s)²`) the bracket is bounded by `C/2+s+1`, and the bulk
  `∫ saddleDensity` over that strip is `o(mainScale)` (same complete-square + the
  already-proved `gaussianTail_left_ratio_tendsto_zero`).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval

noncomputable section

/-- Pointwise bracket bound on the whole shifted ray `x > 0`: `|bracket| ≤ C/2+s+1`. -/
lemma abs_bracket_le_const {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    |C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹| ≤ C / 2 + s + 1 := by
  have hCpos : 0 < C := C_pos
  have hx1 : (1 : ℝ) ≤ x + 1 := by linarith
  have hxpos : (0 : ℝ) < x + 1 := by linarith
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (x + 1) := by
    nlinarith [Real.sq_sqrt hxpos.le, Real.sqrt_nonneg (x + 1), hx1]
  have hsqrtpos : 0 < Real.sqrt (x + 1) := by positivity
  have hterm_le : C / (2 * Real.sqrt (x + 1)) ≤ C / 2 := by
    gcongr <;> nlinarith [hsqrt1, hCpos]
  have hterm_pos : 0 ≤ C / (2 * Real.sqrt (x + 1)) := by positivity
  have hinv_le : (x + 1)⁻¹ ≤ 1 := by
    rw [← one_div]; exact (div_le_one hxpos).mpr hx1
  have hinv_pos : 0 ≤ (x + 1)⁻¹ := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- Pointwise bracket bound on the right region `x+1 ≥ (C/4s)²`: `|bracket| ≤ 2s`
(needs `16s ≤ C²`, eventually true as `s→0⁺`). -/
lemma abs_bracket_le_two_s {s x : ℝ} (hs : 0 < s) (hsmall : 16 * s ≤ C ^ 2)
    (hx : (gaussianTailCut s) ^ 2 - 1 ≤ x) :
    |C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹| ≤ 2 * s := by
  have hCpos : 0 < C := C_pos
  have hcutpos : 0 < C / (4 * s) := by positivity
  have hcutle : (C / (4 * s)) ^ 2 ≤ x + 1 := by
    have h2 : (gaussianTailCut s) ^ 2 ≤ x + 1 := by linarith [hx]
    rwa [show gaussianTailCut s = C / (4 * s) from rfl] at h2
  have hxpos : 0 < x + 1 := by nlinarith [hcutpos, hcutle]
  have hsqrtpos : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr hxpos
  have hsqrtcut : C / (4 * s) ≤ Real.sqrt (x + 1) := by
    nlinarith [Real.sq_sqrt hxpos.le, Real.sqrt_nonneg (x + 1), hcutle, hcutpos]
  have hcleared : C ≤ 4 * s * Real.sqrt (x + 1) := by
    have h := hsqrtcut
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * s)] at h
    linarith [h]
  have hupper : C / (2 * Real.sqrt (x + 1)) ≤ 2 * s := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt (x + 1))]
    nlinarith [hcleared]
  have hterm_pos : 0 ≤ C / (2 * Real.sqrt (x + 1)) := by positivity
  have hmul : C ^ 2 ≤ 16 * s ^ 2 * (x + 1) := by
    have h := hcutle
    rw [show (C / (4 * s)) ^ 2 = C ^ 2 / (16 * s ^ 2) by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < 16 * s ^ 2)] at h
    linarith [h]
  have hinv_le : (x + 1)⁻¹ ≤ s := by
    rw [← one_div, div_le_iff₀ hxpos]
    nlinarith [hmul, hsmall, hs]
  have hinv_pos : 0 ≤ (x + 1)⁻¹ := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- The bracket-weighted error integrand is integrable on `(0,∞)` (dominated by
`(C/2+s+1)·saddleDensity s (·+1)`). -/
lemma integrableOn_errIntegrand {s : ℝ} (hs : 0 < s) :
    IntegrableOn
      (fun x => |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
      (Set.Ioi (0 : ℝ)) := by
  have hCpos : 0 < C := C_pos
  have hmeas : AEStronglyMeasurable
      (fun x => |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply Measurable.aestronglyMeasurable; unfold saddleDensity; fun_prop
  have hdom : IntegrableOn (fun x => (C / 2 + s + 1) * saddleDensity s (x + 1)) (Set.Ioi 0) :=
    (integrableOn_saddleDensity_shift hs).const_mul _
  refine hdom.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  have hx0 : 0 < x := hx
  have hxpos : 0 < x + 1 := by linarith
  have hsd : 0 ≤ saddleDensity s (x + 1) := by rw [saddleDensity]; positivity
  rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_nonneg hsd]
  calc saddleDensity s (x + 1) * |C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹|
      ≤ saddleDensity s (x + 1) * (C / 2 + s + 1) :=
        mul_le_mul_of_nonneg_left (abs_bracket_le_const hs hx0) hsd
    _ = (C / 2 + s + 1) * saddleDensity s (x + 1) := by ring

/-- The left bulk `∫_{Ioc 0 (cut²−1)} saddleDensity s (·+1)` equals
`2 e^{A/s}·∫_{Ioc 1 cut} e^{-s(v-v₀)²}/v` (translation + `x=v²` + complete square). -/
lemma leftBulk_eq {s : ℝ} (hs : 0 < s) (hcut : 1 ≤ gaussianTailCut s) :
    (∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
      = 2 * Real.exp (Partitions.A / s) *
          ∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s),
            Real.exp (-s * (v - C / (2 * s)) ^ 2) / v := by
  set cut := gaussianTailCut s with hcutdef
  have hxc0 : (0 : ℝ) ≤ cut ^ 2 - 1 := by nlinarith [hcut]
  rw [← intervalIntegral.integral_of_le hxc0,
    intervalIntegral.integral_comp_add_right (saddleDensity s) 1,
    show (0 : ℝ) + 1 = 1 by norm_num, show cut ^ 2 - 1 + 1 = cut ^ 2 by ring,
    modelSaddleInterval_substitution hcut]
  have hcong : (∫ v in (1 : ℝ)..cut, 2 * Real.exp (C * v - s * v ^ 2) / v)
      = ∫ v in (1 : ℝ)..cut,
          2 * Real.exp (Partitions.A / s) * (Real.exp (-s * (v - C / (2 * s)) ^ 2) / v) := by
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [saddle_complete_square hs v, show Partitions.A / s - s * (v - C / (2 * s)) ^ 2
        = Partitions.A / s + -s * (v - C / (2 * s)) ^ 2 by ring, Real.exp_add]
    ring
  rw [hcong, intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hcut]

/-- Domain-split bound: the error integral `≤ (C/2+s+1)·LeftBulk + 2s·shiftIntegral`. -/
lemma errIntegral_le {s : ℝ} (hs : 0 < s) (hsmall : 16 * s ≤ C ^ 2)
    (hcut : 1 ≤ gaussianTailCut s) :
    (∫ x in Set.Ioi (0 : ℝ),
        |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
      ≤ (C / 2 + s + 1) *
          (∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
        + 2 * s * (∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) := by
  have hCpos : 0 < C := C_pos
  set xc := (gaussianTailCut s) ^ 2 - 1 with hxcdef
  have hxc0 : (0 : ℝ) ≤ xc := by nlinarith [hcut]
  have hsub_Ioc : Set.Ioc (0 : ℝ) xc ⊆ Set.Ioi 0 := fun x hx => hx.1
  have hsub_Ioi : Set.Ioi xc ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_le_of_lt hxc0 hx
  have hF := integrableOn_errIntegrand hs
  have hFIoc := hF.mono_set hsub_Ioc
  have hFIoi := hF.mono_set hsub_Ioi
  have hsd := integrableOn_saddleDensity_shift hs
  have hsdIoc := hsd.mono_set hsub_Ioc
  have hsdIoixc := hsd.mono_set hsub_Ioi
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) xc) (Set.Ioi xc) := by
    refine Set.disjoint_left.mpr (fun y hy1 hy2 => ?_)
    exact absurd (Set.mem_Ioi.mp hy2) (not_lt.mpr hy1.2)
  have hunion := setIntegral_union hdisj measurableSet_Ioi hFIoc hFIoi
  rw [Set.Ioc_union_Ioi_eq_Ioi hxc0] at hunion
  -- sd union for the monotonicity step
  have hunion_sd := setIntegral_union hdisj measurableSet_Ioi hsdIoc hsdIoixc
  rw [Set.Ioc_union_Ioi_eq_Ioi hxc0] at hunion_sd
  have hLBnn : 0 ≤ ∫ x in Set.Ioc (0 : ℝ) xc, saddleDensity s (x + 1) :=
    setIntegral_nonneg measurableSet_Ioc (fun x hx => by
      have hpos : 0 < x + 1 := by linarith [hx.1]
      rw [saddleDensity]; positivity)
  have hmono : (∫ x in Set.Ioi xc, saddleDensity s (x + 1))
      ≤ ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1) := by
    rw [hunion_sd]; linarith [hLBnn]
  rw [hunion]
  have hleft : (∫ x in Set.Ioc (0 : ℝ) xc,
        |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
      ≤ (C / 2 + s + 1) * ∫ x in Set.Ioc (0 : ℝ) xc, saddleDensity s (x + 1) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hFIoc (hsdIoc.const_mul _) measurableSet_Ioc
    intro x hx
    have hx0 : 0 < x := hx.1
    have hsdnn : 0 ≤ saddleDensity s (x + 1) := by rw [saddleDensity]; positivity
    rw [abs_mul, abs_of_nonneg hsdnn]
    calc saddleDensity s (x + 1) * |C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹|
        ≤ saddleDensity s (x + 1) * (C / 2 + s + 1) :=
          mul_le_mul_of_nonneg_left (abs_bracket_le_const hs hx0) hsdnn
      _ = (C / 2 + s + 1) * saddleDensity s (x + 1) := by ring
  have hright : (∫ x in Set.Ioi xc,
        |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
      ≤ 2 * s * ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1) := by
    have hstep : (∫ x in Set.Ioi xc,
          |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
        ≤ 2 * s * ∫ x in Set.Ioi xc, saddleDensity s (x + 1) := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on hFIoi (hsdIoixc.const_mul _) measurableSet_Ioi
      intro x hx
      have hxxc : xc ≤ x := le_of_lt (Set.mem_Ioi.mp hx)
      have hx0 : 0 < x := lt_of_le_of_lt hxc0 (Set.mem_Ioi.mp hx)
      have hsdnn : 0 ≤ saddleDensity s (x + 1) := by rw [saddleDensity]; positivity
      rw [abs_mul, abs_of_nonneg hsdnn]
      calc saddleDensity s (x + 1) * |C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹|
          ≤ saddleDensity s (x + 1) * (2 * s) :=
            mul_le_mul_of_nonneg_left (abs_bracket_le_two_s hs hsmall hxxc) hsdnn
        _ = 2 * s * saddleDensity s (x + 1) := by ring
    calc (∫ x in Set.Ioi xc,
          |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
        ≤ 2 * s * ∫ x in Set.Ioi xc, saddleDensity s (x + 1) := hstep
      _ ≤ 2 * s * ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
  linarith [hleft, hright]

/-- `LeftBulk / mainScale → 0` (the substituted strip ratio, via
`gaussianTail_left_ratio_tendsto_zero`). -/
lemma leftBulk_div_mainScale_tendsto_zero :
    Tendsto (fun s : ℝ =>
        (∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
          / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine gaussianTail_left_ratio_tendsto_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_one_le_cut] with s hs hcut
  have hspos : 0 < s := hs
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  have hexpne : Real.exp (Partitions.A / s) ≠ 0 := Real.exp_ne_zero _
  have hCne : C ≠ 0 := ne_of_gt hCpos
  rw [leftBulk_eq hspos hcut]
  unfold mainScale
  set I := ∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s),
    Real.exp (-s * (v - C / (2 * s)) ^ 2) / v with hI
  field_simp
  ring

/-- The bracket-weighted error integral over `mainScale` tends to `0`. -/
lemma errIntegral_div_mainScale_tendsto_zero :
    Tendsto (fun s : ℝ =>
        (∫ x in Set.Ioi (0 : ℝ),
            |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
          / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hCpos : 0 < C := C_pos
  have hT1 := shiftIntegral_div_mainScale_tendsto_one
  have hLB := leftBulk_div_mainScale_tendsto_zero
  have hconst : Tendsto (fun s : ℝ => C / 2 + s + 1) (𝓝[>] (0 : ℝ)) (𝓝 (C / 2 + 0 + 1)) :=
    ((tendsto_const_nhds (x := C / 2)).add (tendsto_id.mono_left nhdsWithin_le_nhds)).add
      (tendsto_const_nhds (x := (1 : ℝ)))
  have hL : Tendsto (fun s : ℝ => (C / 2 + s + 1) *
      ((∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
        / mainScale s)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := hconst.mul hLB; simpa using this
  have h2s : Tendsto (fun s : ℝ => 2 * s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => 2 * s) (𝓝 (0 : ℝ)) (𝓝 (2 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun s : ℝ => 2 * s *
      ((∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) / mainScale s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using h2s.mul hT1
  have hupper := hL.add hR
  rw [add_zero] at hupper
  have hsmall_ev : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 16 * s ≤ C ^ 2 := by
    have h16 : Tendsto (fun s : ℝ => 16 * s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ => 16 * s) (𝓝 (0 : ℝ)) (𝓝 (16 * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact h16.eventually_le_const (pow_pos hCpos 2)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hms := mainScale_pos hs
    exact div_nonneg (setIntegral_nonneg measurableSet_Ioi (fun x _ => abs_nonneg _)) hms.le
  · filter_upwards [self_mem_nhdsWithin, eventually_one_le_cut, hsmall_ev] with s hs hcut hsmall
    have hspos : 0 < s := hs
    have hms : 0 < mainScale s := mainScale_pos hspos
    rw [div_le_iff₀ hms]
    have hexpand : ((C / 2 + s + 1) *
          ((∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
            / mainScale s)
        + 2 * s * ((∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) / mainScale s)) * mainScale s
        = (C / 2 + s + 1) *
            (∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
          + 2 * s * (∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) := by
      field_simp
    rw [hexpand]
    exact errIntegral_le hspos hsmall hcut

/-- **The mesh-1 Riemann error is negligible** — discharges the last hypothesis. -/
theorem riemannError_negligible : RiemannErrorNegligible := by
  have hCpos : 0 < C := C_pos
  have herr := errIntegral_div_mainScale_tendsto_zero
  have hexp : Tendsto (fun s : ℝ => Real.exp (C * Real.sqrt 3) / mainScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_const_nhds.div_atTop mainScale_tendsto_atTop
  have hsum := herr.add hexp
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [add_div]

end
end AnalyticCombinatorics.Ch8.Partitions

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions
open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval
theorem solution {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto Erdos.u atTop (𝓝 a)) :
    a = 1 / (4 * Real.sqrt 3) :=
  erdos_limit_constant ha hlim riemannError_negligible
