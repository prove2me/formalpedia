-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.partition_log_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-25T13:51:26.554813+00:00
-- url     : https://prove2.me/submissions/36f928be-72f1-48aa-864a-8c94b31b52df

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_LaplaceAsymptotic
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_EulerProduct
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_LaplaceLimit
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_LogAsymptotic
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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

/-!
# A logarithmic Tauberian theorem for cumulative coefficients

This file is intentionally independent of the partition development.  The
results are stated for an arbitrary nonnegative sequence of real coefficients.
-/

open Filter
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Tauberian

noncomputable section

lemma Cum_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    0 ≤ Cum a N := by
  unfold Cum
  exact Finset.sum_nonneg fun n _ => ha n

lemma Cum_pos_of_pos_zero {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : 0 < a 0) (N : ℕ) :
    0 < Cum a N := by
  unfold Cum
  have hmem : 0 ∈ Finset.range (N + 1) := by simp
  exact Finset.sum_pos' (fun n _ => ha n) ⟨0, hmem, ha0⟩

lemma Cum_mono {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    Monotone (Cum a) := by
  intro M N hMN
  unfold Cum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hn)
      (Nat.succ_le_succ hMN))
  · intro n _ _
    exact ha n

lemma term_le_Cum {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    a n ≤ Cum a n := by
  unfold Cum
  have hmem : n ∈ Finset.range (n + 1) := by simp
  exact Finset.single_le_sum (fun m _ => ha m) hmem

lemma Cum_succ (a : ℕ → ℝ) (N : ℕ) :
    Cum a (N + 1) = Cum a N + a (N + 1) := by
  unfold Cum
  rw [show N + 1 + 1 = N + 2 by omega]
  rw [Finset.sum_range_succ]

lemma finite_abel_cum (a : ℕ → ℝ) (q : ℝ) :
    ∀ M : ℕ,
      (1 - q) * (∑ N ∈ Finset.range (M + 1), Cum a N * q ^ N)
        =
      (∑ n ∈ Finset.range (M + 1), a n * q ^ n)
        - Cum a M * q ^ (M + 1)
  | 0 => by
      simp [Cum]
      ring_nf
  | M + 1 => by
      have ih := finite_abel_cum a q M
      rw [Finset.sum_range_succ
        (f := fun N => Cum a N * q ^ N) (n := M + 1)]
      rw [Finset.sum_range_succ
        (f := fun n => a n * q ^ n) (n := M + 1)]
      rw [mul_add, ih, Cum_succ]
      ring_nf
      simp [mul_comm]

theorem laplace_eq_abel_cum_q
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsum : Summable fun n : ℕ => a n * q ^ n) :
    (∑' n : ℕ, a n * q ^ n)
      =
    ∑' N : ℕ, (1 - q) * (Cum a N * q ^ N) := by
  let f : ℕ → ℝ := fun n => a n * q ^ n
  let g : ℕ → ℝ := fun N => (1 - q) * (Cum a N * q ^ N)
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    exact mul_nonneg (ha n) (pow_nonneg hq0 n)
  have hg_nonneg : ∀ N, 0 ≤ g N := by
    intro N
    dsimp [g]
    exact mul_nonneg (sub_nonneg.mpr hq1.le) (mul_nonneg (Cum_nonneg ha N) (pow_nonneg hq0 N))
  have hg_sum_bound : ∀ M : ℕ, ∑ N ∈ Finset.range M, g N ≤ ∑' n : ℕ, f n := by
    intro M
    cases M with
    | zero =>
        simpa [g] using tsum_nonneg hf_nonneg
    | succ M =>
        have hfin := finite_abel_cum a q M
        have htail_nonneg : 0 ≤ Cum a M * q ^ (M + 1) :=
          mul_nonneg (Cum_nonneg ha M) (pow_nonneg hq0 (M + 1))
        have hpartial :
            (1 - q) * (∑ N ∈ Finset.range (M + 1), Cum a N * q ^ N)
              ≤ ∑ n ∈ Finset.range (M + 1), a n * q ^ n := by
          linarith
        have hpartial_tsum :
            ∑ n ∈ Finset.range (M + 1), a n * q ^ n ≤ ∑' n : ℕ, f n := by
          simpa [f] using
            hsum.sum_le_tsum (Finset.range (M + 1)) (fun n _ => hf_nonneg n)
        calc
          ∑ N ∈ Finset.range (M + 1), g N
              = (1 - q) * (∑ N ∈ Finset.range (M + 1), Cum a N * q ^ N) := by
                simp [g, Finset.mul_sum]
          _ ≤ ∑ n ∈ Finset.range (M + 1), a n * q ^ n := hpartial
          _ ≤ ∑' n : ℕ, f n := hpartial_tsum
  have hg_summable : Summable g :=
    summable_of_sum_range_le hg_nonneg hg_sum_bound
  have htail_zero :
      Tendsto (fun M : ℕ => Cum a M * q ^ (M + 1)) atTop (𝓝 0) := by
    have hg_zero : Tendsto g atTop (𝓝 0) := hg_summable.tendsto_atTop_zero
    have hconst := hg_zero.const_mul (q / (1 - q))
    have hconst0 : Tendsto (fun M : ℕ => (q / (1 - q)) * g M) atTop (𝓝 0) := by
      simpa using hconst
    refine hconst0.congr' ?_
    filter_upwards with M
    dsimp [g]
    have hne : 1 - q ≠ 0 := by linarith
    field_simp [hne]
    rw [pow_succ']
    ring_nf
  have hsum_f_nat :
      Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, f n) atTop
        (𝓝 (∑' n : ℕ, f n)) :=
    hsum.hasSum.tendsto_sum_nat
  have hsum_g_nat :
      Tendsto (fun M : ℕ => ∑ N ∈ Finset.range M, g N) atTop
        (𝓝 (∑' N : ℕ, g N)) :=
    hg_summable.hasSum.tendsto_sum_nat
  have hlim_right :
      Tendsto
        (fun M : ℕ => (∑ n ∈ Finset.range (M + 1), f n) - Cum a M * q ^ (M + 1))
        atTop
        (𝓝 ((∑' n : ℕ, f n) - 0)) :=
    (hsum_f_nat.comp (tendsto_add_atTop_nat 1)).sub htail_zero
  have hlim_left :
      Tendsto (fun M : ℕ => ∑ N ∈ Finset.range (M + 1), g N) atTop
        (𝓝 (∑' N : ℕ, g N)) :=
    hsum_g_nat.comp (tendsto_add_atTop_nat 1)
  have heq_seq :
      (fun M : ℕ => ∑ N ∈ Finset.range (M + 1), g N)
        =ᶠ[atTop]
      (fun M : ℕ => (∑ n ∈ Finset.range (M + 1), f n) - Cum a M * q ^ (M + 1)) := by
    refine Eventually.of_forall ?_
    intro M
    have hfin := finite_abel_cum a q M
    dsimp [f, g]
    rw [← hfin]
    simp [Finset.mul_sum]
  have hlim_left' :
      Tendsto (fun M : ℕ => ∑ N ∈ Finset.range (M + 1), g N) atTop
        (𝓝 ((∑' n : ℕ, f n) - 0)) :=
    hlim_right.congr' heq_seq.symm
  have huniq := tendsto_nhds_unique hlim_left hlim_left'
  simpa [f, g, sub_zero] using huniq.symm

theorem laplace_eq_abel_cum
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    {t : ℝ} (ht : 0 < t)
    (hsum : Summable fun n : ℕ => a n * Real.exp (-(t * n))) :
    (∑' n : ℕ, a n * Real.exp (-(t * n)))
      =
    (1 - Real.exp (-t))
      * ∑' N : ℕ, Cum a N * Real.exp (-(t * N)) := by
  let q : ℝ := Real.exp (-t)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hpow : ∀ n : ℕ, q ^ n = Real.exp (-(t * n)) := by
    intro n
    dsimp [q]
    rw [← Real.exp_nat_mul]
    ring_nf
  have hsum_q : Summable fun n : ℕ => a n * q ^ n := by
    refine hsum.congr ?_
    intro n
    rw [hpow n]
  have habel := laplace_eq_abel_cum_q a ha hq0 hq1 hsum_q
  calc
    (∑' n : ℕ, a n * Real.exp (-(t * n)))
        = ∑' n : ℕ, a n * q ^ n := by
          apply tsum_congr
          intro n
          rw [hpow n]
    _ = ∑' N : ℕ, (1 - q) * (Cum a N * q ^ N) := habel
    _ = (1 - q) * ∑' N : ℕ, Cum a N * q ^ N := by
          rw [tsum_mul_left]
    _ = (1 - Real.exp (-t))
      * ∑' N : ℕ, Cum a N * Real.exp (-(t * N)) := by
          dsimp [q]
          congr 1
          apply tsum_congr
          intro N
          rw [hpow N]

lemma laplace_term_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {t : ℝ} (n : ℕ) :
    0 ≤ a n * Real.exp (-(t * n)) := by
  exact mul_nonneg (ha n) (Real.exp_pos _).le

lemma Cum_mul_exp_le_laplace_sum
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {t : ℝ} (ht : 0 < t) (N : ℕ) :
    Cum a N * Real.exp (-(t * N))
      ≤ ∑ n ∈ Finset.range (N + 1), a n * Real.exp (-(t * n)) := by
  unfold Cum
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro n hn
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hexp :
      Real.exp (-(t * (N : ℝ))) ≤ Real.exp (-(t * (n : ℝ))) := by
    refine Real.exp_monotone ?_
    have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    nlinarith [mul_le_mul_of_nonneg_left hnN' ht.le]
  exact mul_le_mul_of_nonneg_left hexp (ha n)

lemma Cum_mul_exp_le_laplace_tsum
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {t : ℝ} (ht : 0 < t)
    (hsum : Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (N : ℕ) :
    Cum a N * Real.exp (-(t * N))
      ≤ ∑' n : ℕ, a n * Real.exp (-(t * n)) := by
  exact (Cum_mul_exp_le_laplace_sum ha ht N).trans
    (hsum.sum_le_tsum (Finset.range (N + 1)) (fun n _ => laplace_term_nonneg ha n))

lemma laplace_tsum_pos_of_pos_zero
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : 0 < a 0)
    {t : ℝ} (hsum : Summable fun n : ℕ => a n * Real.exp (-(t * n))) :
    0 < ∑' n : ℕ, a n * Real.exp (-(t * n)) := by
  have h0 : 0 < a 0 * Real.exp (-(t * (0 : ℕ))) := by
    simpa using ha0
  exact hsum.tsum_pos (fun n => laplace_term_nonneg ha n) 0 h0

lemma exp_quadratic_lower {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 4 ≤ Real.exp x := by
  have hlin : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ x / 2) (Real.exp_pos _).le).mpr hlin
  calc
    x ^ 2 / 4 = (x / 2) ^ 2 := by ring_nf
    _ ≤ Real.exp (x / 2) ^ 2 := hsq
    _ = Real.exp x := by
      rw [sq, ← Real.exp_add]
      set_option backward.isDefEq.respectTransparency false in
        ring_nf

lemma one_sub_exp_neg_ge_half {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have hpos : 0 < 1 + u := by linarith
  have hexp_ge : 1 + u ≤ Real.exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  have hinv : (Real.exp u)⁻¹ ≤ (1 + u)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) hpos).mpr hexp_ge
  have hden : u / (1 + u) ≤ 1 - Real.exp (-u) := by
    rw [Real.exp_neg]
    calc
      u / (1 + u) = 1 - (1 + u)⁻¹ := by
        field_simp [hpos.ne']
        ring_nf
      _ ≤ 1 - (Real.exp u)⁻¹ := by linarith
  have hhalf : u / 2 ≤ u / (1 + u) := by
    field_simp [hpos.ne']
    nlinarith
  exact hhalf.trans hden

lemma geom_inv_le_exp_eventually {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (1 - Real.exp (-(θ * t)))⁻¹ ≤ Real.exp (c / t) := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t ≤ min (1 / θ) (θ * c ^ 2 / 8) :=
    by
      have hnhds : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
          t ≤ min (1 / θ) (θ * c ^ 2 / 8) :=
        Iic_mem_nhds (show (0 : ℝ) < min (1 / θ) (θ * c ^ 2 / 8) by
          exact lt_min (one_div_pos.mpr hθ) (by positivity))
      exact hnhds.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht_small
  have htpos : 0 < t := ht
  have ht_le₁ : t ≤ 1 / θ := ht_small.trans (min_le_left _ _)
  have ht_le₂ : t ≤ θ * c ^ 2 / 8 := ht_small.trans (min_le_right _ _)
  have hu0 : 0 ≤ θ * t := mul_nonneg hθ.le htpos.le
  have hu1 : θ * t ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left ht_le₁ hθ.le
    simpa [one_div, hθ.ne'] using hmul
  have hden_lower : θ * t / 2 ≤ 1 - Real.exp (-(θ * t)) :=
    one_sub_exp_neg_ge_half hu0 hu1
  have hden_pos : 0 < 1 - Real.exp (-(θ * t)) := by
    have hhalf_pos : 0 < θ * t / 2 := by positivity
    exact hhalf_pos.trans_le hden_lower
  have hinv_le : (1 - Real.exp (-(θ * t)))⁻¹ ≤ (θ * t / 2)⁻¹ :=
    (inv_le_inv₀ hden_pos (by positivity : 0 < θ * t / 2)).mpr hden_lower
  have hrat_le : (θ * t / 2)⁻¹ ≤ Real.exp (c / t) := by
    have hx_nonneg : 0 ≤ c / t := by positivity
    have hquad := exp_quadratic_lower hx_nonneg
    have hposct : 0 < c / t := div_pos hc htpos
    have htarget : (θ * t / 2)⁻¹ ≤ (c / t) ^ 2 / 4 := by
      field_simp [hθ.ne', htpos.ne', hc.ne']
      nlinarith [ht_le₂, hθ, hc, htpos, sq_pos_of_pos hc]
    exact htarget.trans hquad
  exact hinv_le.trans hrat_le

lemma exp_sqrt_sub_linear_le
    {B lam t : ℝ} (_hB : 0 ≤ B) (hlam : 0 < lam) (ht : 0 < t) (N : ℕ) :
    B * Real.sqrt (N : ℝ) - t * N
      ≤ B ^ 2 / (4 * lam * t) - (1 - lam) * t * N := by
  let x : ℝ := Real.sqrt (N : ℝ)
  have hx2 : x ^ 2 = (N : ℝ) := by
    dsimp [x]
    exact Real.sq_sqrt (by positivity)
  have hbasic : B * x ≤ lam * t * x ^ 2 + B ^ 2 / (4 * lam * t) := by
    have hsq : 0 ≤ (2 * lam * t * x - B) ^ 2 := sq_nonneg _
    have hden : 0 < 4 * lam * t := by positivity
    have hscaled := div_nonneg hsq hden.le
    have hident :
        (2 * lam * t * x - B) ^ 2 / (4 * lam * t)
          = lam * t * x ^ 2 - B * x + B ^ 2 / (4 * lam * t) := by
      field_simp [hlam.ne', ht.ne']
      ring_nf
    rw [hident] at hscaled
    linarith
  have hbasicN :
      B * Real.sqrt (N : ℝ) ≤ lam * t * (N : ℝ) + B ^ 2 / (4 * lam * t) := by
    simpa [x, hx2] using hbasic
  nlinarith [hbasicN]

lemma exp_sqrt_sub_linear_bound
    {B lam t : ℝ} (hB : 0 ≤ B) (hlam : 0 < lam) (ht : 0 < t) (N : ℕ) :
    Real.exp (B * Real.sqrt (N : ℝ) - t * N)
      ≤ Real.exp (B ^ 2 / (4 * lam * t)) *
        Real.exp (-((1 - lam) * t) * N) := by
  have h := exp_sqrt_sub_linear_le (B := B) (lam := lam) (t := t) hB hlam ht N
  calc
    Real.exp (B * Real.sqrt (N : ℝ) - t * N)
        ≤ Real.exp (B ^ 2 / (4 * lam * t) - (1 - lam) * t * N) :=
          Real.exp_monotone h
    _ = Real.exp (B ^ 2 / (4 * lam * t)) *
        Real.exp (-((1 - lam) * t) * N) := by
      rw [← Real.exp_add]
      set_option backward.isDefEq.respectTransparency false in
        ring_nf

lemma exp_sqrt_sub_linear_summable
    {B t : ℝ} (ht : 0 < t) :
    Summable fun N : ℕ => Real.exp (B * Real.sqrt (N : ℝ) - t * N) := by
  by_cases hB : 0 ≤ B
  · have hdom :
        ∀ N : ℕ,
          Real.exp (B * Real.sqrt (N : ℝ) - t * N)
            ≤ Real.exp (B ^ 2 / (4 * ((1 : ℝ) / 2) * t)) *
              Real.exp (-(((1 : ℝ) - (1 : ℝ) / 2) * t) * N) := by
      intro N
      exact exp_sqrt_sub_linear_bound (B := B) (lam := (1 : ℝ) / 2) (t := t) hB
        (by norm_num) ht N
    have hgeom : Summable fun N : ℕ => Real.exp (-(((1 : ℝ) - (1 : ℝ) / 2) * t) * N) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.summable_exp_nat_mul_iff.mpr (by nlinarith [ht] :
          -(((1 : ℝ) - (1 : ℝ) / 2) * t) < 0))
    have hnonneg :
        ∀ N : ℕ, 0 ≤ Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
      fun N => (Real.exp_pos _).le
    exact (hgeom.mul_left
      (Real.exp (B ^ 2 / (4 * ((1 : ℝ) / 2) * t)))).of_nonneg_of_le hnonneg hdom
  · have hBle : B ≤ 0 := le_of_not_ge hB
    have hdom :
        ∀ N : ℕ,
          Real.exp (B * Real.sqrt (N : ℝ) - t * N)
            ≤ Real.exp (-(t * N)) := by
      intro N
      refine Real.exp_monotone ?_
      have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hBle hsqrt_nonneg]
    have hgeom : Summable fun N : ℕ => Real.exp (-(t * N)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr ht))
    have hnonneg :
        ∀ N : ℕ, 0 ≤ Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
      fun N => (Real.exp_pos _).le
    exact hgeom.of_nonneg_of_le hnonneg hdom

lemma tsum_exp_neg_mul_nat {r : ℝ} (hr : 0 < r) :
    (∑' N : ℕ, Real.exp (-r * N)) = (1 - Real.exp (-r))⁻¹ := by
  have h0 : 0 ≤ Real.exp (-r) := (Real.exp_pos _).le
  have h1 : Real.exp (-r) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hr)
  have hgeom := tsum_geometric_of_lt_one h0 h1
  calc
    (∑' N : ℕ, Real.exp (-r * N)) = ∑' N : ℕ, (Real.exp (-r)) ^ N := by
      apply tsum_congr
      intro N
      rw [← Real.exp_nat_mul]
      ring_nf
    _ = (1 - Real.exp (-r))⁻¹ := hgeom

lemma exists_lam_for_quadratic_gap {K B : ℝ}
    (hK : 0 < K) (hBsq : B ^ 2 / 4 < K) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ B ^ 2 / (4 * lam) < K := by
  let A : ℝ := B ^ 2 / 4
  let lam : ℝ := (A + K) / (2 * K)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA_lt : A < K := by simpa [A] using hBsq
  have hden : 0 < 2 * K := by positivity
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    positivity
  have hlam_lt : lam < 1 := by
    dsimp [lam]
    rw [div_lt_one hden]
    nlinarith
  have hsum_pos : 0 < A + K := by positivity
  have hcoef_eq : B ^ 2 / (4 * lam) = (2 * A * K) / (A + K) := by
    dsimp [A, lam]
    field_simp [hK.ne']
  have hcoef_lt : B ^ 2 / (4 * lam) < K := by
    rw [hcoef_eq]
    rw [div_lt_iff₀ hsum_pos]
    nlinarith
  exact ⟨lam, hlam_pos, hlam_lt, hcoef_lt⟩

theorem sqrt_laplace_full_gap_of_sq_lt
    {K B : ℝ} (hK : 0 < K) (hB : 0 ≤ B) (hBsq : B ^ 2 / 4 < K) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (∑' N : ℕ, Real.exp (B * Real.sqrt (N : ℝ) - t * N))
          ≤ Real.exp ((K - ρ) / t) := by
  rcases exists_lam_for_quadratic_gap hK hBsq with ⟨lam, hlam_pos, hlam_lt, hcoef_lt⟩
  let C : ℝ := B ^ 2 / (4 * lam)
  let θ : ℝ := 1 - lam
  have hθ : 0 < θ := by
    dsimp [θ]
    exact sub_pos.mpr hlam_lt
  let ρ : ℝ := (K - C) / 2
  have hρ : 0 < ρ := by
    dsimp [ρ, C]
    linarith
  refine ⟨ρ, hρ, ?_⟩
  have hgeom_event := geom_inv_le_exp_eventually hθ hρ
  filter_upwards [self_mem_nhdsWithin, hgeom_event] with t ht hgeom_inv
  have htpos : 0 < t := ht
  have hdom :
      ∀ N : ℕ,
        Real.exp (B * Real.sqrt (N : ℝ) - t * N)
          ≤ Real.exp (C / t) * Real.exp (-(θ * t) * N) := by
    intro N
    have h0 := exp_sqrt_sub_linear_bound (B := B) (lam := lam) (t := t) hB hlam_pos htpos N
    have hC :
        B ^ 2 / (4 * lam * t) = C / t := by
      dsimp [C]
      field_simp [hlam_pos.ne', htpos.ne']
    have hθeq :
        -((1 - lam) * t) * (N : ℝ) = -(θ * t) * (N : ℝ) := by
      dsimp [θ]
    simpa [hC, hθeq] using h0
  have hgeom_summable : Summable fun N : ℕ => Real.exp (-(θ * t) * N) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.summable_exp_nat_mul_iff.mpr (by nlinarith [hθ, htpos] : -(θ * t) < 0))
  have hmajor_summable :
      Summable fun N : ℕ => Real.exp (C / t) * Real.exp (-(θ * t) * N) :=
    hgeom_summable.mul_left (Real.exp (C / t))
  have hleft_summable :
      Summable fun N : ℕ => Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
    hmajor_summable.of_nonneg_of_le (fun N => (Real.exp_pos _).le) hdom
  calc
    (∑' N : ℕ, Real.exp (B * Real.sqrt (N : ℝ) - t * N))
        ≤ ∑' N : ℕ, Real.exp (C / t) * Real.exp (-(θ * t) * N) :=
          hleft_summable.tsum_le_tsum hdom hmajor_summable
    _ = Real.exp (C / t) * (∑' N : ℕ, Real.exp (-(θ * t) * N)) := by
          rw [tsum_mul_left]
    _ = Real.exp (C / t) * (1 - Real.exp (-(θ * t)))⁻¹ := by
          rw [tsum_exp_neg_mul_nat (mul_pos hθ htpos)]
    _ ≤ Real.exp (C / t) * Real.exp (ρ / t) := by
          exact mul_le_mul_of_nonneg_left hgeom_inv (Real.exp_pos _).le
    _ = Real.exp ((K - ρ) / t) := by
          rw [← Real.exp_add]
          dsimp [ρ, C]
          field_simp [htpos.ne']
          ring_nf

lemma sq_div_four_lt_of_nonneg_lt_two_sqrt
    {K B : ℝ} (hK : 0 < K) (hB0 : 0 ≤ B)
    (hBlt : B < 2 * Real.sqrt K) :
    B ^ 2 / 4 < K := by
  have hsqrt_nonneg : 0 ≤ 2 * Real.sqrt K := by positivity
  have hsq : B ^ 2 < (2 * Real.sqrt K) ^ 2 :=
    (sq_lt_sq₀ hB0 hsqrt_nonneg).mpr hBlt
  rw [mul_pow, Real.sq_sqrt hK.le] at hsq
  nlinarith

theorem sqrt_laplace_full_gap
    {K B : ℝ} (hK : 0 < K) (hBlt : B < 2 * Real.sqrt K) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (∑' N : ℕ, Real.exp (B * Real.sqrt (N : ℝ) - t * N))
          ≤ Real.exp ((K - ρ) / t) := by
  by_cases hB0 : 0 ≤ B
  · exact sqrt_laplace_full_gap_of_sq_lt hK hB0
      (sq_div_four_lt_of_nonneg_lt_two_sqrt hK hB0 hBlt)
  · have hBle : B ≤ 0 := le_of_not_ge hB0
    rcases sqrt_laplace_full_gap_of_sq_lt (B := 0) hK (by norm_num)
        (by simpa using hK) with ⟨ρ, hρ, hEv⟩
    refine ⟨ρ, hρ, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hEv] with t ht hsum
    have htpos : 0 < t := ht
    have hdom :
        ∀ N : ℕ,
          Real.exp (B * Real.sqrt (N : ℝ) - t * N)
            ≤ Real.exp (0 * Real.sqrt (N : ℝ) - t * N) := by
      intro N
      refine Real.exp_monotone ?_
      have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hBle hsqrt_nonneg]
    have hleft : Summable fun N : ℕ => Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
      exp_sqrt_sub_linear_summable htpos
    have hright : Summable fun N : ℕ => Real.exp (0 * Real.sqrt (N : ℝ) - t * N) :=
      exp_sqrt_sub_linear_summable (B := 0) htpos
    exact (hleft.tsum_le_tsum hdom hright).trans hsum

theorem sqrt_laplace_bad_inside_gap
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (1 - Real.exp (-t))
          *
        (∑' N : ℕ,
          Real.exp ((2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) - t * N))
        ≤ Real.exp ((K - ρ) / t) := by
  have hBlt : 2 * Real.sqrt K - ε < 2 * Real.sqrt K := by linarith
  rcases sqrt_laplace_full_gap (K := K) (B := 2 * Real.sqrt K - ε) hK hBlt with
    ⟨ρ, hρ, hEv⟩
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hEv] with t ht hsum
  have hfac_le : 1 - Real.exp (-t) ≤ 1 := by
    linarith [Real.exp_pos (-t)]
  have htsum_nonneg :
      0 ≤ ∑' N : ℕ,
        Real.exp ((2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) - t * N) :=
    tsum_nonneg fun N => (Real.exp_pos _).le
  have hprod_le :
      (1 - Real.exp (-t))
          *
        (∑' N : ℕ,
          Real.exp ((2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) - t * N))
        ≤
        (∑' N : ℕ,
          Real.exp ((2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) - t * N)) := by
    simpa using mul_le_mul_of_nonneg_right hfac_le htsum_nonneg
  exact hprod_le.trans hsum

lemma log_Cum_le_laplace
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : 0 < a 0)
    {t : ℝ} (ht : 0 < t)
    (hsum : Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (N : ℕ) :
    Real.log (Cum a N)
      ≤ t * N + Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))) := by
  have hcum_pos : 0 < Cum a N := Cum_pos_of_pos_zero ha ha0 N
  have hleft_pos : 0 < Cum a N * Real.exp (-(t * N)) :=
    mul_pos hcum_pos (Real.exp_pos _)
  have hle := Cum_mul_exp_le_laplace_tsum ha ht hsum N
  have hlogle := Real.log_le_log hleft_pos hle
  have hexp_ne : Real.exp (-(t * (N : ℝ))) ≠ 0 := (Real.exp_pos _).ne'
  have hcum_ne : Cum a N ≠ 0 := hcum_pos.ne'
  rw [Real.log_mul hcum_ne hexp_ne, Real.log_exp] at hlogle
  nlinarith

end
end AnalyticCombinatorics.Ch8.Partitions.Tauberian

/-!
# Full logarithmic Tauberian estimates for cumulative coefficients

This file continues the elementary Tauberian argument from `Tauberian.lean`.
-/

open Filter
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Tauberian

noncomputable section

lemma sqrt_one_add_sub_one_sq_ge_delta_sq_div_sixteen
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    δ ^ 2 / 16 ≤ (Real.sqrt (1 + δ) - 1) ^ 2 := by
  let y : ℝ := Real.sqrt (1 + δ)
  have hc0 : 0 ≤ 1 + δ := by linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = 1 + δ := by
    dsimp [y]
    exact Real.sq_sqrt hc0
  have hy_ge_one : 1 ≤ y := by
    have hsq : (1 : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by norm_num) hy_nonneg).mp hsq
  have hy_le_two : y ≤ 2 := by
    have hsq : y ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith
    exact (sq_le_sq₀ hy_nonneg (by norm_num)).mp hsq
  have hδ_eq : δ = (y - 1) * (y + 1) := by nlinarith
  have hδ_le : δ ≤ 4 * (y - 1) := by
    have hy1_nonneg : 0 ≤ y - 1 := by linarith
    nlinarith
  have hbase : δ / 4 ≤ y - 1 := by linarith
  have hbase_nonneg : 0 ≤ δ / 4 := by positivity
  have hy1_nonneg : 0 ≤ y - 1 := by linarith
  have hsquare : (δ / 4) ^ 2 ≤ (y - 1) ^ 2 :=
    (sq_le_sq₀ hbase_nonneg hy1_nonneg).mpr hbase
  have htarget : δ ^ 2 / 16 = (δ / 4) ^ 2 := by ring
  simpa [y, htarget]
    using hsquare

lemma delta_div_four_le_sqrt_one_add_sub_one
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    δ / 4 ≤ Real.sqrt (1 + δ) - 1 := by
  let y : ℝ := Real.sqrt (1 + δ)
  have hc0 : 0 ≤ 1 + δ := by linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = 1 + δ := by
    dsimp [y]
    exact Real.sq_sqrt hc0
  have hy_ge_one : 1 ≤ y := by
    have hsq : (1 : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by norm_num) hy_nonneg).mp hsq
  have hy_le_two : y ≤ 2 := by
    have hsq : y ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith
    exact (sq_le_sq₀ hy_nonneg (by norm_num)).mp hsq
  have hδ_eq : δ = (y - 1) * (y + 1) := by nlinarith
  have hδ_le : δ ≤ 4 * (y - 1) := by
    have hy1_nonneg : 0 ≤ y - 1 := by linarith
    nlinarith
  simpa [y] using (show δ / 4 ≤ y - 1 by linarith)

lemma sqrt_one_sub_sub_one_sq_ge_delta_sq_div_sixteen
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    δ ^ 2 / 16 ≤ (Real.sqrt (1 - δ) - 1) ^ 2 := by
  let y : ℝ := Real.sqrt (1 - δ)
  have hc0 : 0 ≤ 1 - δ := by linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = 1 - δ := by
    dsimp [y]
    exact Real.sq_sqrt hc0
  have hy_le_one : y ≤ 1 := by
    have hsq : y ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith
    exact (sq_le_sq₀ hy_nonneg (by norm_num)).mp hsq
  have hδ_eq : δ = (1 - y) * (1 + y) := by nlinarith
  have hδ_le : δ ≤ 4 * (1 - y) := by
    have hy1_nonneg : 0 ≤ 1 - y := by linarith
    nlinarith
  have hbase : δ / 4 ≤ 1 - y := by linarith
  have hbase_nonneg : 0 ≤ δ / 4 := by positivity
  have hy1_nonneg : 0 ≤ 1 - y := by linarith
  have hsquare : (δ / 4) ^ 2 ≤ (1 - y) ^ 2 :=
    (sq_le_sq₀ hbase_nonneg hy1_nonneg).mpr hbase
  have htarget : δ ^ 2 / 16 = (δ / 4) ^ 2 := by ring
  have hsign : (y - 1) ^ 2 = (1 - y) ^ 2 := by ring
  simpa [y, htarget, hsign]
    using hsquare

lemma sqrt_one_add_delta_le_two {δ : ℝ} (hδ1 : δ < 1) :
    Real.sqrt (1 + δ) ≤ 2 := by
  by_cases hc0 : 0 ≤ 1 + δ
  · have hsq : (Real.sqrt (1 + δ)) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt hc0]
      nlinarith
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp hsq
  · have hsqrt_zero : Real.sqrt (1 + δ) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hc0)
    nlinarith

lemma sqrt_one_sub_delta_le_one {δ : ℝ} (hδ0 : 0 < δ) :
    Real.sqrt (1 - δ) ≤ 1 := by
  by_cases hc0 : 0 ≤ 1 - δ
  · have hsq : (Real.sqrt (1 - δ)) ^ 2 ≤ (1 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt hc0]
      nlinarith
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp hsq
  · have hsqrt_zero : Real.sqrt (1 - δ) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hc0)
    nlinarith

lemma sqrt_sub_mul_sqrt_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
  calc
    (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y)
        = (Real.sqrt x) ^ 2 - (Real.sqrt y) ^ 2 := by ring
    _ = x - y := by rw [Real.sq_sqrt hx, Real.sq_sqrt hy]

lemma exponent_le_boundary_of_le
    {B t M x : ℝ} (ht : 0 < t) (hM : 0 < M)
    (hx0 : 0 ≤ x) (hxM : x ≤ M)
    (hcrit : t * (2 * Real.sqrt M) ≤ B) :
    B * Real.sqrt x - t * x ≤ B * Real.sqrt M - t * M := by
  have hM_nonneg : 0 ≤ M := hM.le
  have hsqrtx_le : Real.sqrt x ≤ Real.sqrt M := Real.sqrt_le_sqrt hxM
  have hsqrt_diff_nonneg : 0 ≤ Real.sqrt M - Real.sqrt x := by linarith
  have hsum_le : Real.sqrt M + Real.sqrt x ≤ 2 * Real.sqrt M := by linarith
  have htsum_le : t * (Real.sqrt M + Real.sqrt x) ≤ t * (2 * Real.sqrt M) :=
    mul_le_mul_of_nonneg_left hsum_le ht.le
  have hfactor : 0 ≤ B - t * (Real.sqrt M + Real.sqrt x) := by linarith
  have hdiff :
      B * Real.sqrt M - t * M - (B * Real.sqrt x - t * x)
        =
      (Real.sqrt M - Real.sqrt x) * (B - t * (Real.sqrt M + Real.sqrt x)) := by
    have hid := sqrt_sub_mul_sqrt_add hM_nonneg hx0
    nlinarith
  have hprod : 0 ≤ (Real.sqrt M - Real.sqrt x) * (B - t * (Real.sqrt M + Real.sqrt x)) :=
    mul_nonneg hsqrt_diff_nonneg hfactor
  nlinarith

lemma sqrt_le_tangent
    {M x : ℝ} (hM : 0 < M) (hxM : M ≤ x) :
    Real.sqrt x ≤ Real.sqrt M + (x - M) / (2 * Real.sqrt M) := by
  have hM_nonneg : 0 ≤ M := hM.le
  have hx_nonneg : 0 ≤ x := hM_nonneg.trans hxM
  have hsqrtM_pos : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hsqrtM_le : Real.sqrt M ≤ Real.sqrt x := Real.sqrt_le_sqrt hxM
  have hsum_pos : 0 < Real.sqrt x + Real.sqrt M := by positivity
  have hid :
      Real.sqrt x - Real.sqrt M
        = (x - M) / (Real.sqrt x + Real.sqrt M) := by
    field_simp [hsum_pos.ne']
    calc
      (Real.sqrt x - Real.sqrt M) * (Real.sqrt x + Real.sqrt M)
          = (Real.sqrt x) ^ 2 - (Real.sqrt M) ^ 2 := by ring
      _ = x - M := by rw [Real.sq_sqrt hx_nonneg, Real.sq_sqrt hM_nonneg]
  have hden_le : 2 * Real.sqrt M ≤ Real.sqrt x + Real.sqrt M := by
    nlinarith
  have hnum_nonneg : 0 ≤ x - M := by linarith
  have hfrac_le :
      (x - M) / (Real.sqrt x + Real.sqrt M)
        ≤ (x - M) / (2 * Real.sqrt M) := by
    exact div_le_div_of_nonneg_left hnum_nonneg (by positivity) hden_le
  nlinarith

lemma exponent_upper_decay
    {B t M x s : ℝ} (hB : 0 ≤ B) (hM : 0 < M) (hxM : M ≤ x)
    (hs : s * t ≤ t - B / (2 * Real.sqrt M)) :
    B * Real.sqrt x - t * x
      ≤ B * Real.sqrt M - t * M - s * t * (x - M) := by
  have htangent := sqrt_le_tangent hM hxM
  have hdiff_nonneg : 0 ≤ x - M := by linarith
  have hstep :
      B * Real.sqrt x - t * x
        ≤ B * Real.sqrt M - t * M - (t - B / (2 * Real.sqrt M)) * (x - M) := by
    have hB_tangent :
        B * Real.sqrt x
          ≤ B * (Real.sqrt M + (x - M) / (2 * Real.sqrt M)) := by
      exact mul_le_mul_of_nonneg_left htangent hB
    have hsqrtM_pos : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
    calc
      B * Real.sqrt x - t * x
          ≤ B * (Real.sqrt M + (x - M) / (2 * Real.sqrt M)) - t * x := by
            linarith
      _ = B * Real.sqrt M - t * M - (t - B / (2 * Real.sqrt M)) * (x - M) := by
            field_simp [hsqrtM_pos.ne']
            ring
  have hcoef :
      s * t * (x - M) ≤ (t - B / (2 * Real.sqrt M)) * (x - M) :=
    mul_le_mul_of_nonneg_right hs hdiff_nonneg
  nlinarith

lemma const_le_exp_inv_eventually {D c : ℝ} (hc : 0 < c) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, D ≤ Real.exp (c / t) := by
  let A : ℝ := max (D - 1) 1
  have hApos : 0 < A := by
    dsimp [A]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ c / A := by
    have hnhds : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t ≤ c / A :=
      Iic_mem_nhds (by positivity)
    exact hnhds.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht_small
  have hAle : A ≤ c / t := by
    rw [le_div_iff₀ ht]
    have hmul := mul_le_mul_of_nonneg_left ht_small hApos.le
    have hAc : A * (c / A) = c := by field_simp [hApos.ne']
    nlinarith
  have hDle : D ≤ 1 + c / t := by
    have hDminus : D - 1 ≤ A := by
      dsimp [A]
      exact le_max_left _ _
    linarith
  have hexp : 1 + c / t ≤ Real.exp (c / t) := by
    simpa [add_comm] using Real.add_one_le_exp (c / t)
  exact hDle.trans hexp

lemma inv_sq_linear_absorb_eventually {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, A / t ^ 2 + 1 ≤ Real.exp (c / t) := by
  let D : ℝ := A * 16 / c ^ 2 + 1
  have hhalf : 0 < c / 2 := by positivity
  have hconst := const_le_exp_inv_eventually (D := D) hhalf
  filter_upwards [self_mem_nhdsWithin, hconst] with t ht hD
  have htpos : 0 < t := ht
  let E : ℝ := Real.exp ((c / 2) / t)
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  have hEnonneg : 0 ≤ E := hEpos.le
  have hEge_one : 1 ≤ E := by
    have hx0 : 0 ≤ (c / 2) / t := by positivity
    have h := Real.add_one_le_exp ((c / 2) / t)
    dsimp [E]
    linarith
  have hquad0 : 0 ≤ (c / 2) / t := by positivity
  have hquad := exp_quadratic_lower hquad0
  have hquad' : c ^ 2 / (16 * t ^ 2) ≤ E := by
    dsimp [E]
    calc
      c ^ 2 / (16 * t ^ 2) = ((c / 2) / t) ^ 2 / 4 := by
        field_simp [htpos.ne']
        ring
      _ ≤ Real.exp ((c / 2) / t) := hquad
  have hAterm : A / t ^ 2 ≤ (A * 16 / c ^ 2) * E := by
    have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_pos hc
    have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_pos htpos
    have hcoef_nonneg : 0 ≤ A * 16 / c ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hquad' hcoef_nonneg
    calc
      A / t ^ 2 = (A * 16 / c ^ 2) * (c ^ 2 / (16 * t ^ 2)) := by
        field_simp [hc.ne', htpos.ne']
      _ ≤ (A * 16 / c ^ 2) * E := hmul
  have hsum : A / t ^ 2 + 1 ≤ D * E := by
    dsimp [D]
    nlinarith
  have hprod : D * E ≤ E * E := by
    exact mul_le_mul_of_nonneg_right hD hEnonneg
  calc
    A / t ^ 2 + 1 ≤ D * E := hsum
    _ ≤ E * E := hprod
    _ = Real.exp (c / t) := by
      dsimp [E]
      rw [← Real.exp_add]
      congr 1
      field_simp [htpos.ne']
      ring

lemma boundary_exponent_eq
    {K c α t : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (ht : 0 < t) :
    ((2 + α) * Real.sqrt K) * Real.sqrt (c * K / t ^ 2)
        - t * (c * K / t ^ 2)
      =
    (K / t) * ((2 + α) * Real.sqrt c - c) := by
  have ht_ne : t ≠ 0 := ht.ne'
  have hsqrt :
      Real.sqrt (c * K / t ^ 2) = Real.sqrt c * Real.sqrt K / t := by
    rw [Real.sqrt_div (mul_nonneg hc hK)]
    rw [Real.sqrt_mul hc]
    rw [Real.sqrt_sq ht.le]
  have hsqrtK_sq : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK
  rw [hsqrt]
  field_simp [ht_ne]
  ring_nf
  rw [hsqrtK_sq]
  ring

lemma sqrt_mul_div_sq_eq
    {K c t : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (ht : 0 < t) :
    Real.sqrt (c * K / t ^ 2) = Real.sqrt c * Real.sqrt K / t := by
  rw [Real.sqrt_div (mul_nonneg hc hK)]
  rw [Real.sqrt_mul hc]
  rw [Real.sqrt_sq ht.le]

lemma lower_boundary_coef_le
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (2 + δ ^ 2 / 64) * Real.sqrt (1 - δ) - (1 - δ)
      ≤ 1 - δ ^ 2 / 32 := by
  let y : ℝ := Real.sqrt (1 - δ)
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hc0 : 0 ≤ 1 - δ := by linarith
  have hy_sq : y ^ 2 = 1 - δ := by
    dsimp [y]
    exact Real.sq_sqrt hc0
  have hy_le_one : y ≤ 1 := by simpa [y] using sqrt_one_sub_delta_le_one hδ0
  have hmargin : δ ^ 2 / 16 ≤ (y - 1) ^ 2 := by
    simpa [y] using sqrt_one_sub_sub_one_sq_ge_delta_sq_div_sixteen hδ0 hδ1
  have hδsq_nonneg : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hsmall : δ ^ 2 / 64 * y ≤ δ ^ 2 / 64 := by
    nlinarith
  have hbase : 2 * y - y ^ 2 ≤ 1 - δ ^ 2 / 16 := by
    nlinarith
  have hcalc :
      (2 + δ ^ 2 / 64) * y - y ^ 2
        ≤ 1 - δ ^ 2 / 32 := by
    nlinarith
  calc
    (2 + δ ^ 2 / 64) * Real.sqrt (1 - δ) - (1 - δ)
        = (2 + δ ^ 2 / 64) * y - y ^ 2 := by
          dsimp [y]
          rw [hy_sq]
    _ ≤ 1 - δ ^ 2 / 32 := hcalc

lemma upper_boundary_coef_le
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (2 + δ ^ 2 / 64) * Real.sqrt (1 + δ) - (1 + δ)
      ≤ 1 - δ ^ 2 / 32 := by
  let y : ℝ := Real.sqrt (1 + δ)
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hc0 : 0 ≤ 1 + δ := by linarith
  have hy_sq : y ^ 2 = 1 + δ := by
    dsimp [y]
    exact Real.sq_sqrt hc0
  have hy_le_two : y ≤ 2 := by simpa [y] using sqrt_one_add_delta_le_two hδ1
  have hmargin : δ ^ 2 / 16 ≤ (y - 1) ^ 2 := by
    simpa [y] using sqrt_one_add_sub_one_sq_ge_delta_sq_div_sixteen hδ0 hδ1
  have hδsq_nonneg : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hsmall : δ ^ 2 / 64 * y ≤ δ ^ 2 / 32 := by
    nlinarith
  have hbase : 2 * y - y ^ 2 ≤ 1 - δ ^ 2 / 16 := by
    nlinarith
  have hcalc :
      (2 + δ ^ 2 / 64) * y - y ^ 2
        ≤ 1 - δ ^ 2 / 32 := by
    nlinarith
  simpa [y, hy_sq, mul_add, add_mul, sub_eq_add_neg] using hcalc

lemma lower_boundary_exponent_le
    {K δ t : ℝ} (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) :
    (2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64))
        * Real.sqrt ((1 - δ) * K / t ^ 2)
        - t * ((1 - δ) * K / t ^ 2)
      ≤ (K - K * δ ^ 2 / 32) / t := by
  have hc : 0 ≤ 1 - δ := by linarith
  have hB :
      2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)
        = (2 + δ ^ 2 / 64) * Real.sqrt K := by ring
  have heq := boundary_exponent_eq (K := K) (c := 1 - δ)
    (α := δ ^ 2 / 64) (t := t) hK.le hc ht
  have hcoef := lower_boundary_coef_le hδ0 hδ1
  calc
    (2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64))
        * Real.sqrt ((1 - δ) * K / t ^ 2)
        - t * ((1 - δ) * K / t ^ 2)
        = (K / t) *
            ((2 + δ ^ 2 / 64) * Real.sqrt (1 - δ) - (1 - δ)) := by
          rw [hB, heq]
    _ ≤ (K / t) * (1 - δ ^ 2 / 32) := by
          exact mul_le_mul_of_nonneg_left hcoef (div_nonneg hK.le ht.le)
    _ = (K - K * δ ^ 2 / 32) / t := by
          field_simp [ht.ne']

lemma upper_boundary_exponent_le
    {K δ t : ℝ} (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) :
    (2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64))
        * Real.sqrt ((1 + δ) * K / t ^ 2)
        - t * ((1 + δ) * K / t ^ 2)
      ≤ (K - K * δ ^ 2 / 32) / t := by
  have hc : 0 ≤ 1 + δ := by linarith
  have hB :
      2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)
        = (2 + δ ^ 2 / 64) * Real.sqrt K := by ring
  have heq := boundary_exponent_eq (K := K) (c := 1 + δ)
    (α := δ ^ 2 / 64) (t := t) hK.le hc ht
  have hcoef := upper_boundary_coef_le hδ0 hδ1
  calc
    (2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64))
        * Real.sqrt ((1 + δ) * K / t ^ 2)
        - t * ((1 + δ) * K / t ^ 2)
        = (K / t) *
            ((2 + δ ^ 2 / 64) * Real.sqrt (1 + δ) - (1 + δ)) := by
          rw [hB, heq]
    _ ≤ (K / t) * (1 - δ ^ 2 / 32) := by
          exact mul_le_mul_of_nonneg_left hcoef (div_nonneg hK.le ht.le)
    _ = (K - K * δ ^ 2 / 32) / t := by
          field_simp [ht.ne']

lemma strong_gap_s_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < 1 - (1 + δ ^ 2 / 128) / Real.sqrt (1 + δ) := by
  have hypos : 0 < Real.sqrt (1 + δ) := by positivity
  have hgap := delta_div_four_le_sqrt_one_add_sub_one hδ0 hδ1
  have halpha_lt : δ ^ 2 / 128 < δ / 4 := by nlinarith [hδ0, hδ1]
  have hnum_lt : 1 + δ ^ 2 / 128 < Real.sqrt (1 + δ) := by linarith
  have hfrac_lt : (1 + δ ^ 2 / 128) / Real.sqrt (1 + δ) < 1 := by
    exact (div_lt_one hypos).mpr hnum_lt
  linarith

lemma lower_tail_tsum_bound
    {K δ t : ℝ} (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) :
    (∑' N : ℕ,
      if (N : ℝ) ≤ (1 - δ) * K / t ^ 2 then
        Real.exp
          ((2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)) * Real.sqrt (N : ℝ)
            - t * N)
      else 0)
      ≤
    ((Nat.floor ((1 - δ) * K / t ^ 2) : ℝ) + 1)
      * Real.exp ((K - K * δ ^ 2 / 32) / t) := by
  let L : ℝ := (1 - δ) * K / t ^ 2
  let B : ℝ := 2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)
  let C : ℝ := Real.exp ((K - K * δ ^ 2 / 32) / t)
  have hLpos : 0 < L := by
    dsimp [L]
    exact div_pos (mul_pos (by linarith) hK) (sq_pos_of_pos ht)
  have hL_nonneg : 0 ≤ L := hLpos.le
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hcrit : t * (2 * Real.sqrt L) ≤ B := by
    have hsqrtL := sqrt_mul_div_sq_eq (K := K) (c := 1 - δ) (t := t)
      hK.le (by linarith) ht
    have hsqrt_le_one : Real.sqrt (1 - δ) ≤ 1 := sqrt_one_sub_delta_le_one hδ0
    have hsqrtK_nonneg : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
    dsimp [L, B] at hsqrtL ⊢
    rw [hsqrtL]
    field_simp [ht.ne']
    nlinarith [mul_le_mul_of_nonneg_right hsqrt_le_one hsqrtK_nonneg,
      sq_nonneg δ]
  have hboundary := lower_boundary_exponent_le hK hδ0 hδ1 ht
  let f : ℕ → ℝ := fun N =>
    if (N : ℝ) ≤ L then
      Real.exp (B * Real.sqrt (N : ℝ) - t * N)
    else 0
  have hzero : ∀ N ∉ Finset.range (Nat.floor L + 1), f N = 0 := by
    intro N hN
    have hnotlt : ¬N < Nat.floor L + 1 := by
      simpa [Finset.mem_range] using hN
    have hge : Nat.floor L + 1 ≤ N := Nat.le_of_not_lt hnotlt
    have hfloor_lt : Nat.floor L < N := Nat.lt_of_succ_le hge
    have hLlt : L < (N : ℝ) := (Nat.floor_lt hL_nonneg).mp hfloor_lt
    dsimp [f]
    simp [not_le.mpr hLlt]
  have hpoint :
      ∀ N ∈ Finset.range (Nat.floor L + 1), f N ≤ C := by
    intro N _hN
    dsimp [f]
    split_ifs with hNL
    · have hmono := exponent_le_boundary_of_le (B := B) (t := t) (M := L) (x := (N : ℝ))
        ht hLpos (by positivity) hNL hcrit
      have hbd :
          B * Real.sqrt L - t * L ≤ (K - K * δ ^ 2 / 32) / t := by
        dsimp [B, L]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hboundary
      exact Real.exp_monotone (hmono.trans hbd)
    · dsimp [C]
      positivity
  calc
    (∑' N : ℕ,
      if (N : ℝ) ≤ (1 - δ) * K / t ^ 2 then
        Real.exp
          ((2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)) * Real.sqrt (N : ℝ)
            - t * N)
      else 0)
        = ∑' N : ℕ, f N := by
          apply tsum_congr
          intro N
          simp [f, L, B]
    _ = ∑ N ∈ Finset.range (Nat.floor L + 1), f N := by
          exact tsum_eq_sum hzero
    _ ≤ ∑ _N ∈ Finset.range (Nat.floor L + 1), C := by
          exact Finset.sum_le_sum hpoint
    _ = ((Nat.floor L : ℝ) + 1) * C := by
          simp [Finset.sum_const, Nat.cast_add, Nat.cast_one]
    _ =
      ((Nat.floor ((1 - δ) * K / t ^ 2) : ℝ) + 1)
        * Real.exp ((K - K * δ ^ 2 / 32) / t) := by
          rfl

lemma upper_tail_tsum_bound
    {K δ t : ℝ} (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) :
    let s : ℝ := 1 - (1 + δ ^ 2 / 128) / Real.sqrt (1 + δ)
    (∑' N : ℕ,
      if (1 + δ) * K / t ^ 2 ≤ (N : ℝ) then
        Real.exp
          ((2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)) * Real.sqrt (N : ℝ)
            - t * N)
      else 0)
      ≤
    Real.exp ((K - K * δ ^ 2 / 32) / t)
      * (1 - Real.exp (-(s * t)))⁻¹ := by
  intro s
  let U : ℝ := (1 + δ) * K / t ^ 2
  let B : ℝ := 2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)
  let C : ℝ := Real.exp ((K - K * δ ^ 2 / 32) / t)
  let n0 : ℕ := Nat.ceil U
  let u : ℕ → ℝ := fun N =>
    if U ≤ (N : ℝ) then Real.exp (B * Real.sqrt (N : ℝ) - t * N) else 0
  have hUpos : 0 < U := by
    dsimp [U]
    exact div_pos (mul_pos (by linarith) hK) (sq_pos_of_pos ht)
  have hU_nonneg : 0 ≤ U := hUpos.le
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hs_pos : 0 < s := by
    dsimp [s]
    exact strong_gap_s_pos hδ0 hδ1
  have hst_pos : 0 < s * t := mul_pos hs_pos ht
  have hslope : s * t ≤ t - B / (2 * Real.sqrt U) := by
    have hsqrtU := sqrt_mul_div_sq_eq (K := K) (c := 1 + δ) (t := t)
      hK.le (by linarith) ht
    have hsqrtK_pos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
    have hsqrtc_pos : 0 < Real.sqrt (1 + δ) := by positivity
    dsimp [s, U, B] at hsqrtU ⊢
    rw [hsqrtU]
    field_simp [ht.ne', hsqrtK_pos.ne', hsqrtc_pos.ne']
    ring_nf
    linarith
  have hboundary := upper_boundary_exponent_le hK hδ0 hδ1 ht
  have hu_nonneg : ∀ N, 0 ≤ u N := by
    intro N
    dsimp [u]
    split <;> positivity
  have hu_le_full :
      ∀ N, u N ≤ Real.exp (B * Real.sqrt (N : ℝ) - t * N) := by
    intro N
    dsimp [u]
    split
    · rfl
    · positivity
  have hfull_summable :
      Summable fun N : ℕ => Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
    exp_sqrt_sub_linear_summable ht
  have hu_summable : Summable u :=
    hfull_summable.of_nonneg_of_le hu_nonneg hu_le_full
  have hrange_zero : ∑ N ∈ Finset.range n0, u N = 0 := by
    refine Finset.sum_eq_zero ?_
    intro N hN
    have hNlt : N < n0 := Finset.mem_range.mp hN
    have hnot : ¬ U ≤ (N : ℝ) := by
      intro hUN
      have hn0le : n0 ≤ N := (Nat.ceil_le).mpr hUN
      omega
    dsimp [u]
    simp [hnot]
  have hsplit := Summable.sum_add_tsum_nat_add n0 hu_summable
  have htail_eq :
      (∑' k : ℕ, u (k + n0)) = ∑' N : ℕ, u N := by
    simpa [hrange_zero] using hsplit
  have htail_point :
      ∀ k : ℕ,
        u (k + n0) ≤ C * Real.exp (-(s * t) * k) := by
    intro k
    have hceil : U ≤ (n0 : ℝ) := Nat.le_ceil U
    have hNgeU : U ≤ ((k + n0 : ℕ) : ℝ) := by
      exact hceil.trans (by exact_mod_cast Nat.le_add_left n0 k)
    have hdist : (k : ℝ) ≤ ((k + n0 : ℕ) : ℝ) - U := by
      have hcast : ((k + n0 : ℕ) : ℝ) = (k : ℝ) + (n0 : ℝ) := by norm_num
      rw [hcast]
      nlinarith
    have hdecay := exponent_upper_decay (B := B) (t := t) (M := U)
      (x := ((k + n0 : ℕ) : ℝ)) (s := s) hB_nonneg hUpos hNgeU hslope
    have hbd :
        B * Real.sqrt U - t * U ≤ (K - K * δ ^ 2 / 32) / t := by
      dsimp [B, U]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hboundary
    have hdist_decay :
        -(s * t) * (((k + n0 : ℕ) : ℝ) - U) ≤ -(s * t) * (k : ℝ) := by
      exact mul_le_mul_of_nonpos_left hdist (by nlinarith [hst_pos])
    have hexp_arg :
        B * Real.sqrt (((k + n0 : ℕ) : ℝ)) - t * ((k + n0 : ℕ) : ℝ)
          ≤ (K - K * δ ^ 2 / 32) / t - s * t * (k : ℝ) := by
      nlinarith
    calc
      u (k + n0)
          = Real.exp
            (B * Real.sqrt (((k + n0 : ℕ) : ℝ)) - t * ((k + n0 : ℕ) : ℝ)) := by
              dsimp [u]
              rw [if_pos hNgeU]
      _ ≤ Real.exp ((K - K * δ ^ 2 / 32) / t - s * t * (k : ℝ)) :=
            Real.exp_monotone hexp_arg
      _ = C * Real.exp (-(s * t) * k) := by
            dsimp [C]
            rw [← Real.exp_add]
            congr 1
            ring
  have hgeom_summable : Summable fun k : ℕ => C * Real.exp (-(s * t) * k) := by
    have hgeom : Summable fun k : ℕ => Real.exp (-(s * t) * k) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.summable_exp_nat_mul_iff.mpr (by nlinarith [hst_pos] : -(s * t) < 0))
    exact hgeom.mul_left C
  have htail_summable : Summable fun k : ℕ => u (k + n0) := by
    exact (summable_nat_add_iff n0).2 hu_summable
  have htail_le :
      (∑' k : ℕ, u (k + n0)) ≤ ∑' k : ℕ, C * Real.exp (-(s * t) * k) :=
    htail_summable.tsum_le_tsum htail_point hgeom_summable
  calc
    (∑' N : ℕ,
      if (1 + δ) * K / t ^ 2 ≤ (N : ℝ) then
        Real.exp
          ((2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)) * Real.sqrt (N : ℝ)
            - t * N)
      else 0)
        = ∑' N : ℕ, u N := by
          apply tsum_congr
          intro N
          simp [u, U, B]
    _ = ∑' k : ℕ, u (k + n0) := htail_eq.symm
    _ ≤ ∑' k : ℕ, C * Real.exp (-(s * t) * k) := htail_le
    _ = C * (1 - Real.exp (-(s * t)))⁻¹ := by
          rw [tsum_mul_left]
          rw [tsum_exp_neg_mul_nat hst_pos]
    _ =
      Real.exp ((K - K * δ ^ 2 / 32) / t)
        * (1 - Real.exp (-(s * t)))⁻¹ := by
          rfl

theorem sqrt_laplace_restricted_gap_strong
    {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧ ∀ᶠ t in 𝓝[>] 0,
      (∑' N : ℕ,
        if (1 - δ) * K / t ^ 2 ≤ (N : ℝ)
            ∧ (N : ℝ) ≤ (1 + δ) * K / t ^ 2 then 0
        else Real.exp ((2 * Real.sqrt K + η) * Real.sqrt (N : ℝ) - t * N))
        ≤ Real.exp ((K - ρ) / t) := by
  let η : ℝ := Real.sqrt K * (δ ^ 2 / 64)
  let R : ℝ := K * δ ^ 2 / 32
  let ρ : ℝ := R / 2
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  refine ⟨η, ρ, hη, hρ, ?_⟩
  let s : ℝ := 1 - (1 + δ ^ 2 / 128) / Real.sqrt (1 + δ)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact strong_gap_s_pos hδ hδ1
  have hquarter : 0 < R / 4 := by positivity
  have hpolyEv := inv_sq_linear_absorb_eventually (A := K) (c := R / 4) hK.le hquarter
  have hgeomEv := geom_inv_le_exp_eventually hs_pos hquarter
  have htwoEv := const_le_exp_inv_eventually (D := (2 : ℝ)) hquarter
  filter_upwards [self_mem_nhdsWithin, hpolyEv, hgeomEv, htwoEv] with t ht hpoly hgeom htwo
  have htpos : 0 < t := ht
  let L : ℝ := (1 - δ) * K / t ^ 2
  let U : ℝ := (1 + δ) * K / t ^ 2
  let B : ℝ := 2 * Real.sqrt K + η
  let B0 : ℝ := 2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)
  let C0 : ℝ := Real.exp ((K - R) / t)
  have hB_eq : B = B0 := by
    dsimp [B, B0, η]
  have hB0_nonneg : 0 ≤ B0 := by
    dsimp [B0]
    positivity
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact div_nonneg (mul_nonneg (by linarith : 0 ≤ 1 - δ) hK.le) (sq_nonneg t)
  have hU_nonneg : 0 ≤ U := by
    dsimp [U]
    exact div_nonneg (mul_nonneg (by linarith : 0 ≤ 1 + δ) hK.le) (sq_nonneg t)
  let rterm : ℕ → ℝ := fun N =>
    if L ≤ (N : ℝ) ∧ (N : ℝ) ≤ U then 0
    else Real.exp (B * Real.sqrt (N : ℝ) - t * N)
  let lterm : ℕ → ℝ := fun N =>
    if (N : ℝ) ≤ L then Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) else 0
  let uterm : ℕ → ℝ := fun N =>
    if U ≤ (N : ℝ) then Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) else 0
  have hpoint : ∀ N, rterm N ≤ lterm N + uterm N := by
    intro N
    dsimp [rterm, lterm, uterm]
    by_cases hwin : L ≤ (N : ℝ) ∧ (N : ℝ) ≤ U
    · simp [hwin]
      positivity
    · rw [if_neg hwin]
      by_cases hNL : (N : ℝ) ≤ L
      · rw [if_pos hNL]
        have hBsubst :
            Real.exp (B * Real.sqrt (N : ℝ) - t * N)
              = Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) := by
          rw [hB_eq]
        rw [hBsubst]
        by_cases hUN : U ≤ (N : ℝ)
        · rw [if_pos hUN]
          linarith [Real.exp_pos (B0 * Real.sqrt (N : ℝ) - t * N)]
        · rw [if_neg hUN]
          linarith
      · have hLN : L ≤ (N : ℝ) := le_of_lt (lt_of_not_ge hNL)
        have hnotNU : ¬ (N : ℝ) ≤ U := by
          intro hNU
          exact hwin ⟨hLN, hNU⟩
        have hUN : U ≤ (N : ℝ) := le_of_lt (lt_of_not_ge hnotNU)
        rw [if_neg hNL, if_pos hUN]
        have hBsubst :
            Real.exp (B * Real.sqrt (N : ℝ) - t * N)
              = Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) := by
          rw [hB_eq]
        rw [hBsubst]
        linarith
  have hfull_summable :
      Summable fun N : ℕ => Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) :=
    exp_sqrt_sub_linear_summable htpos
  have hl_nonneg : ∀ N, 0 ≤ lterm N := by
    intro N
    dsimp [lterm]
    split <;> positivity
  have hu_nonneg : ∀ N, 0 ≤ uterm N := by
    intro N
    dsimp [uterm]
    split <;> positivity
  have hr_nonneg : ∀ N, 0 ≤ rterm N := by
    intro N
    dsimp [rterm]
    split <;> positivity
  have hl_le_full :
      ∀ N, lterm N ≤ Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) := by
    intro N
    dsimp [lterm]
    split
    · rfl
    · positivity
  have hu_le_full :
      ∀ N, uterm N ≤ Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) := by
    intro N
    dsimp [uterm]
    split
    · rfl
    · positivity
  have hr_le_full :
      ∀ N, rterm N ≤ Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) := by
    intro N
    dsimp [rterm]
    split
    · positivity
    · rw [hB_eq]
  have hl_summable : Summable lterm :=
    hfull_summable.of_nonneg_of_le hl_nonneg hl_le_full
  have hu_summable : Summable uterm :=
    hfull_summable.of_nonneg_of_le hu_nonneg hu_le_full
  have hr_summable : Summable rterm :=
    hfull_summable.of_nonneg_of_le hr_nonneg hr_le_full
  have hsplit :
      (∑' N : ℕ, rterm N) ≤ (∑' N : ℕ, lterm N) + (∑' N : ℕ, uterm N) := by
    calc
      (∑' N : ℕ, rterm N)
          ≤ ∑' N : ℕ, (lterm N + uterm N) :=
            hr_summable.tsum_le_tsum hpoint (hl_summable.add hu_summable)
      _ = (∑' N : ℕ, lterm N) + (∑' N : ℕ, uterm N) :=
            (hl_summable.tsum_add hu_summable)
  have hlower_raw := lower_tail_tsum_bound hK hδ hδ1 htpos
  have hupper_raw := upper_tail_tsum_bound hK hδ hδ1 htpos
  have hcount_le : ((Nat.floor L : ℝ) + 1) ≤ K / t ^ 2 + 1 := by
    have hfloor_le : (Nat.floor L : ℝ) ≤ L := Nat.floor_le hL_nonneg
    have hL_le : L ≤ K / t ^ 2 := by
      dsimp [L]
      have hden_nonneg : 0 ≤ K / t ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_right (by linarith : 1 - δ ≤ 1) hden_nonneg
      calc
        (1 - δ) * K / t ^ 2 = (1 - δ) * (K / t ^ 2) := by ring
        _ ≤ 1 * (K / t ^ 2) := hmul
        _ = K / t ^ 2 := by ring
    linarith
  have hcount_exp : ((Nat.floor L : ℝ) + 1) ≤ Real.exp ((R / 4) / t) :=
    hcount_le.trans hpoly
  have hlower :
      (∑' N : ℕ, lterm N) ≤ Real.exp ((K - 3 * R / 4) / t) := by
    have hraw :
        (∑' N : ℕ, lterm N)
          ≤ ((Nat.floor L : ℝ) + 1) * C0 := by
      dsimp [lterm, L, B0, C0]
      simpa [R, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hlower_raw
    calc
      (∑' N : ℕ, lterm N)
          ≤ ((Nat.floor L : ℝ) + 1) * C0 := hraw
      _ ≤ Real.exp ((R / 4) / t) * C0 := by
            exact mul_le_mul_of_nonneg_right hcount_exp (by positivity)
      _ = Real.exp ((K - 3 * R / 4) / t) := by
            dsimp [C0]
            rw [← Real.exp_add]
            congr 1
            field_simp [htpos.ne']
            ring
  have hupper :
      (∑' N : ℕ, uterm N) ≤ Real.exp ((K - 3 * R / 4) / t) := by
    have hraw :
        (∑' N : ℕ, uterm N)
          ≤ C0 * (1 - Real.exp (-(s * t)))⁻¹ := by
      dsimp [uterm, U, B0, C0, s]
      simpa [R, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hupper_raw
    calc
      (∑' N : ℕ, uterm N)
          ≤ C0 * (1 - Real.exp (-(s * t)))⁻¹ := hraw
      _ ≤ C0 * Real.exp ((R / 4) / t) := by
            exact mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = Real.exp ((K - 3 * R / 4) / t) := by
            dsimp [C0]
            rw [← Real.exp_add]
            congr 1
            field_simp [htpos.ne']
            ring
  have hsum_two :
      (∑' N : ℕ, rterm N) ≤ 2 * Real.exp ((K - 3 * R / 4) / t) := by
    linarith
  have htwo_absorb :
      2 * Real.exp ((K - 3 * R / 4) / t)
        ≤ Real.exp ((K - R / 2) / t) := by
    calc
      2 * Real.exp ((K - 3 * R / 4) / t)
          ≤ Real.exp ((R / 4) / t) * Real.exp ((K - 3 * R / 4) / t) := by
            exact mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp ((K - R / 2) / t) := by
            rw [← Real.exp_add]
            congr 1
            field_simp [htpos.ne']
            ring
  calc
    (∑' N : ℕ,
        if (1 - δ) * K / t ^ 2 ≤ (N : ℝ)
            ∧ (N : ℝ) ≤ (1 + δ) * K / t ^ 2 then 0
        else Real.exp ((2 * Real.sqrt K + η) * Real.sqrt (N : ℝ) - t * N))
        = ∑' N : ℕ, rterm N := by
          apply tsum_congr
          intro N
          simp [rterm, L, U, B]
    _ ≤ 2 * Real.exp ((K - 3 * R / 4) / t) := hsum_two
    _ ≤ Real.exp ((K - R / 2) / t) := htwo_absorb
    _ = Real.exp ((K - ρ) / t) := by
          dsimp [ρ]

end
end AnalyticCombinatorics.Ch8.Partitions.Tauberian

/-!
# Assembly of the logarithmic Tauberian theorem

This file assembles the already-proved Abel and saddle-window estimates into
the cumulative logarithmic Tauberian theorem.
-/

open Filter
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Tauberian

noncomputable section

private lemma pos_zero_of_one_le {a : ℕ → ℝ} (ha0 : 1 ≤ a 0) : 0 < a 0 := by
  linarith

private lemma laplace_pos_of_one_le
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {t : ℝ}
    (hsum : Summable fun n : ℕ => a n * Real.exp (-(t * n))) :
    0 < ∑' n : ℕ, a n * Real.exp (-(t * n)) :=
  laplace_tsum_pos_of_pos_zero ha (pos_zero_of_one_le ha0) hsum

private lemma Cum_pos_of_one_le
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0) (N : ℕ) :
    0 < Cum a N :=
  Cum_pos_of_pos_zero ha (pos_zero_of_one_le ha0) N

private lemma sqrt_nat_tendsto_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)

private lemma sqrtK_div_sqrtN_tendsto_nhdsWithin_zero
    {K : ℝ} (hK : 0 < K) :
    Tendsto (fun N : ℕ => Real.sqrt K / Real.sqrt (N : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
  have hnhds :
      Tendsto (fun N : ℕ => Real.sqrt K / Real.sqrt (N : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop sqrt_nat_tendsto_atTop
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < Real.sqrt K / Real.sqrt (N : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    exact div_pos (Real.sqrt_pos.mpr hK) (Real.sqrt_pos.mpr hNpos)
  exact tendsto_nhdsWithin_iff.mpr ⟨hnhds, hpos⟩

theorem tauberian_cum_limsup
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {K : ℝ} (hK : 0 < K)
    (hsum : ∀ t > 0, Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (hF :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))))
        (𝓝[>] 0) (𝓝 K)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      Real.log (Cum a N) ≤
        (2 * Real.sqrt K + ε) * Real.sqrt (N : ℝ) := by
  intro ε hε
  have hF_upper :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n)))
          ≤ K + ε * Real.sqrt K :=
    hF.eventually (eventually_le_nhds (by
      have hmul : 0 < ε * Real.sqrt K := by positivity
      linarith))
  have hcomp :
      ∀ᶠ N : ℕ in atTop,
        (Real.sqrt K / Real.sqrt (N : ℝ))
          * Real.log
              (∑' n : ℕ,
                a n * Real.exp (-((Real.sqrt K / Real.sqrt (N : ℝ)) * n)))
          ≤ K + ε * Real.sqrt K :=
    (sqrtK_div_sqrtN_tendsto_nhdsWithin_zero hK).eventually hF_upper
  filter_upwards [eventually_ge_atTop (1 : ℕ), hcomp] with N hN hFN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hsqrtK_pos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  let t : ℝ := Real.sqrt K / Real.sqrt (N : ℝ)
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos hsqrtK_pos hsqrtN_pos
  have hlog_bound :
      Real.log (∑' n : ℕ, a n * Real.exp (-(t * n)))
        ≤ (K + ε * Real.sqrt K) / t := by
    rw [le_div_iff₀ ht]
    simpa [mul_comm, t] using hFN
  have hbase :=
    log_Cum_le_laplace (a := a) ha (pos_zero_of_one_le ha0) (t := t) ht (hsum t ht) N
  have halg :
      t * (N : ℝ) + (K + ε * Real.sqrt K) / t
        = (2 * Real.sqrt K + ε) * Real.sqrt (N : ℝ) := by
    dsimp [t]
    field_simp [hsqrtN_pos.ne', hsqrtK_pos.ne']
    rw [Real.sq_sqrt hK.le, Real.sq_sqrt hNpos.le]
    nlinarith [Real.sq_sqrt hK.le]
  calc
    Real.log (Cum a N)
        ≤ t * (N : ℝ)
            + Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))) := hbase
    _ ≤ t * (N : ℝ) + (K + ε * Real.sqrt K) / t := by linarith
    _ = (2 * Real.sqrt K + ε) * Real.sqrt (N : ℝ) := halg

theorem tauberian_cum_global_bound
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {K : ℝ} (hK : 0 < K)
    (hsum : ∀ t > 0, Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (hF :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))))
        (𝓝[>] 0) (𝓝 K)) :
    ∀ η > 0, ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ,
        Cum a N ≤ C * Real.exp ((2 * Real.sqrt K + η) * Real.sqrt (N : ℝ)) := by
  intro η hη
  let B : ℝ := 2 * Real.sqrt K + η
  have hEv := tauberian_cum_limsup a ha ha0 hK hsum hF η hη
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hEv
  let C0 : ℝ :=
    ∑ N ∈ Finset.range N0,
      Cum a N / Real.exp (B * Real.sqrt (N : ℝ))
  let C : ℝ := max 1 C0
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 C0)
  refine ⟨C, hC_nonneg, ?_⟩
  intro N
  let E : ℝ := Real.exp (B * Real.sqrt (N : ℝ))
  have hEpos : 0 < E := by dsimp [E]; positivity
  by_cases hlt : N < N0
  · have hmem : N ∈ Finset.range N0 := Finset.mem_range.mpr hlt
    have hratio_nonneg :
        ∀ M ∈ Finset.range N0,
          0 ≤ Cum a M / Real.exp (B * Real.sqrt (M : ℝ)) := by
      intro M _hM
      exact div_nonneg (Cum_nonneg ha M) (Real.exp_pos _).le
    have hratio_le_C0 :
        Cum a N / Real.exp (B * Real.sqrt (N : ℝ)) ≤ C0 := by
      dsimp [C0]
      exact Finset.single_le_sum hratio_nonneg hmem
    have hratio_le_C : Cum a N / E ≤ C := by
      dsimp [E, C]
      exact hratio_le_C0.trans (le_max_right 1 C0)
    rwa [div_le_iff₀ hEpos] at hratio_le_C
  · have hge : N0 ≤ N := le_of_not_gt hlt
    have hlog : Real.log (Cum a N) ≤ B * Real.sqrt (N : ℝ) := by
      simpa [B] using hN0 N hge
    have hcum_exp :
        Cum a N ≤ Real.exp (B * Real.sqrt (N : ℝ)) :=
      (Real.log_le_iff_le_exp (Cum_pos_of_one_le ha ha0 N)).mp hlog
    have hCge_one : 1 ≤ C := by
      dsimp [C]
      exact le_max_left 1 C0
    calc
      Cum a N ≤ Real.exp (B * Real.sqrt (N : ℝ)) := hcum_exp
      _ ≤ C * Real.exp (B * Real.sqrt (N : ℝ)) := by
        simpa using mul_le_mul_of_nonneg_right hCge_one (Real.exp_pos _).le

theorem tauberian_exists_large_cum_near_saddle
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {K : ℝ} (hK : 0 < K)
    (hsum : ∀ t > 0, Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (hF :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))))
        (𝓝[>] 0) (𝓝 K))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ t in 𝓝[>] 0, ∃ N : ℕ,
      (1 - δ) * K / t ^ 2 ≤ (N : ℝ) ∧
      (N : ℝ) ≤ (1 + δ) * K / t ^ 2 ∧
      (2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) ≤ Real.log (Cum a N) := by
  rcases sqrt_laplace_bad_inside_gap (K := K) (ε := ε) hK hε with
    ⟨ρw, hρw, hwinGapEv⟩
  rcases sqrt_laplace_restricted_gap_strong (K := K) (δ := δ) hK hδ hδ1 with
    ⟨η, ρo, hη, hρo, hoffGapEv⟩
  rcases tauberian_cum_global_bound a ha ha0 hK hsum hF η hη with
    ⟨C, hC, hglobal⟩
  let r0 : ℝ := min ρw (ρo / 2)
  have hr0 : 0 < r0 := by
    dsimp [r0]
    exact lt_min hρw (half_pos hρo)
  let τ : ℝ := r0 / 2
  have hτ : 0 < τ := by
    dsimp [τ]
    exact half_pos hr0
  have hCabsEv : ∀ᶠ t : ℝ in 𝓝[>] 0, C ≤ Real.exp ((ρo / 2) / t) :=
    const_le_exp_inv_eventually (D := C) (c := ρo / 2) (half_pos hρo)
  have htwoEv : ∀ᶠ t : ℝ in 𝓝[>] 0, (2 : ℝ) ≤ Real.exp (τ / t) :=
    const_le_exp_inv_eventually (D := (2 : ℝ)) (c := τ) hτ
  have hFLowerEv :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        K - τ / 2 ≤
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))) :=
    hF.eventually (eventually_ge_nhds (by
      have hpos : 0 < τ / 2 := half_pos hτ
      linarith))
  filter_upwards
    [self_mem_nhdsWithin, hwinGapEv, hoffGapEv, hCabsEv, htwoEv, hFLowerEv]
    with t ht hwinGap hoffGap hCabs htwo hFLower
  have htpos : 0 < t := ht
  by_contra hno
  let W : ℕ → Prop := fun N =>
    (1 - δ) * K / t ^ 2 ≤ (N : ℝ) ∧
      (N : ℝ) ≤ (1 + δ) * K / t ^ 2
  let Bbad : ℝ := 2 * Real.sqrt K - ε
  let Boff : ℝ := 2 * Real.sqrt K + η
  let full : ℕ → ℝ := fun N => Cum a N * Real.exp (-(t * (N : ℝ)))
  let win : ℕ → ℝ := fun N => if W N then full N else 0
  let off : ℕ → ℝ := fun N => if W N then 0 else full N
  let bad : ℕ → ℝ := fun N =>
    Real.exp (Bbad * Real.sqrt (N : ℝ) - t * (N : ℝ))
  let rterm : ℕ → ℝ := fun N =>
    if W N then 0 else Real.exp (Boff * Real.sqrt (N : ℝ) - t * (N : ℝ))
  let fac : ℝ := 1 - Real.exp (-t)
  have hfac_nonneg : 0 ≤ fac := by
    dsimp [fac]
    have hexp_lt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
    linarith
  have hfac_le_one : fac ≤ 1 := by
    dsimp [fac]
    linarith [Real.exp_pos (-t)]
  have hbad_summable : Summable bad := by
    dsimp [bad, Bbad]
    exact exp_sqrt_sub_linear_summable ht
  have hwin_nonneg : ∀ N, 0 ≤ win N := by
    intro N
    dsimp [win, full]
    split
    · exact mul_nonneg (Cum_nonneg ha N) (Real.exp_pos _).le
    · norm_num
  have hwin_le_bad : ∀ N, win N ≤ bad N := by
    intro N
    dsimp [win, bad]
    by_cases hW : W N
    · simp only [hW, ↓reduceIte, full]
      have hnot :
          ¬ Bbad * Real.sqrt (N : ℝ) ≤ Real.log (Cum a N) := by
        intro hlarge
        exact hno ⟨N, hW.1, hW.2, by simpa [Bbad] using hlarge⟩
      have hlog_lt : Real.log (Cum a N) < Bbad * Real.sqrt (N : ℝ) :=
        not_le.mp hnot
      have hcum_le : Cum a N ≤ Real.exp (Bbad * Real.sqrt (N : ℝ)) :=
        (Real.log_le_iff_le_exp (Cum_pos_of_one_le ha ha0 N)).mp (le_of_lt hlog_lt)
      have hmul :=
        mul_le_mul_of_nonneg_right hcum_le (Real.exp_pos (-(t * (N : ℝ)))).le
      calc
        Cum a N * Real.exp (-(t * (N : ℝ)))
            ≤ Real.exp (Bbad * Real.sqrt (N : ℝ)) * Real.exp (-(t * (N : ℝ))) := hmul
        _ = Real.exp (Bbad * Real.sqrt (N : ℝ) - t * (N : ℝ)) := by
          rw [← Real.exp_add]
          ring_nf
    · simp only [hW, ↓reduceIte]
      positivity
  have hwin_summable : Summable win :=
    hbad_summable.of_nonneg_of_le hwin_nonneg hwin_le_bad
  have hrterm_nonneg : ∀ N, 0 ≤ rterm N := by
    intro N
    dsimp [rterm]
    split <;> positivity
  have hrterm_le_full : ∀ N,
      rterm N ≤ Real.exp (Boff * Real.sqrt (N : ℝ) - t * (N : ℝ)) := by
    intro N
    dsimp [rterm]
    split
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hrterm_summable : Summable rterm :=
    (exp_sqrt_sub_linear_summable (B := Boff) htpos).of_nonneg_of_le
      hrterm_nonneg hrterm_le_full
  have hoff_nonneg : ∀ N, 0 ≤ off N := by
    intro N
    dsimp [off, full]
    split
    · norm_num
    · exact mul_nonneg (Cum_nonneg ha N) (Real.exp_pos _).le
  have hoff_le_Crterm : ∀ N, off N ≤ C * rterm N := by
    intro N
    dsimp [off, rterm]
    by_cases hW : W N
    · simp [hW]
    · simp only [hW, ↓reduceIte, full]
      have hglob : Cum a N ≤ C * Real.exp (Boff * Real.sqrt (N : ℝ)) := by
        simpa [Boff] using hglobal N
      have hmul :=
        mul_le_mul_of_nonneg_right hglob (Real.exp_pos (-(t * (N : ℝ)))).le
      calc
        Cum a N * Real.exp (-(t * (N : ℝ)))
            ≤ (C * Real.exp (Boff * Real.sqrt (N : ℝ)))
                * Real.exp (-(t * (N : ℝ))) := hmul
        _ = C * Real.exp (Boff * Real.sqrt (N : ℝ) - t * (N : ℝ)) := by
          calc
            (C * Real.exp (Boff * Real.sqrt (N : ℝ))) * Real.exp (-(t * (N : ℝ)))
                = C * (Real.exp (Boff * Real.sqrt (N : ℝ))
                    * Real.exp (-(t * (N : ℝ)))) := by ring
            _ = C * Real.exp (Boff * Real.sqrt (N : ℝ) - t * (N : ℝ)) := by
              rw [← Real.exp_add]
              ring_nf
  have hCrterm_summable : Summable fun N : ℕ => C * rterm N :=
    hrterm_summable.mul_left C
  have hoff_summable : Summable off :=
    hCrterm_summable.of_nonneg_of_le hoff_nonneg hoff_le_Crterm
  have hwin_tsum_le : (∑' N : ℕ, win N) ≤ ∑' N : ℕ, bad N :=
    hwin_summable.tsum_le_tsum hwin_le_bad hbad_summable
  have hoff_tsum_le_C :
      (∑' N : ℕ, off N) ≤ C * (∑' N : ℕ, rterm N) := by
    calc
      (∑' N : ℕ, off N)
          ≤ ∑' N : ℕ, C * rterm N :=
            hoff_summable.tsum_le_tsum hoff_le_Crterm hCrterm_summable
      _ = C * (∑' N : ℕ, rterm N) := by
            rw [tsum_mul_left]
  have hbad_gap :
      fac * (∑' N : ℕ, bad N) ≤ Real.exp ((K - ρw) / t) := by
    simpa [fac, bad, Bbad] using hwinGap
  have hrterm_gap :
      (∑' N : ℕ, rterm N) ≤ Real.exp ((K - ρo) / t) := by
    simpa [rterm, W, Boff] using hoffGap
  have hsplit :
      (∑' N : ℕ, full N) = (∑' N : ℕ, win N) + (∑' N : ℕ, off N) := by
    calc
      (∑' N : ℕ, full N)
          = ∑' N : ℕ, (win N + off N) := by
            apply tsum_congr
            intro N
            dsimp [win, off]
            by_cases hW : W N <;> simp [hW]
      _ = (∑' N : ℕ, win N) + (∑' N : ℕ, off N) :=
            (hwin_summable.hasSum.add hoff_summable.hasSum).tsum_eq
  have hwin_part :
      fac * (∑' N : ℕ, win N) ≤ Real.exp ((K - r0) / t) := by
    have hmul : fac * (∑' N : ℕ, win N) ≤ fac * (∑' N : ℕ, bad N) :=
      mul_le_mul_of_nonneg_left hwin_tsum_le hfac_nonneg
    have hr0_le : r0 ≤ ρw := by
      dsimp [r0]
      exact min_le_left _ _
    have hexp_le :
        Real.exp ((K - ρw) / t) ≤ Real.exp ((K - r0) / t) :=
      Real.exp_monotone <|
        div_le_div_of_nonneg_right (by linarith) htpos.le
    exact (hmul.trans hbad_gap).trans hexp_le
  have hoff_part :
      fac * (∑' N : ℕ, off N) ≤ Real.exp ((K - r0) / t) := by
    have hoff_tsum_nonneg : 0 ≤ ∑' N : ℕ, off N :=
      tsum_nonneg hoff_nonneg
    have hfac_drop : fac * (∑' N : ℕ, off N) ≤ ∑' N : ℕ, off N := by
      simpa using mul_le_mul_of_nonneg_right hfac_le_one hoff_tsum_nonneg
    have htoC : fac * (∑' N : ℕ, off N) ≤ C * (∑' N : ℕ, rterm N) :=
      hfac_drop.trans hoff_tsum_le_C
    have htoGap :
        C * (∑' N : ℕ, rterm N) ≤ C * Real.exp ((K - ρo) / t) :=
      mul_le_mul_of_nonneg_left hrterm_gap hC
    have habsorb :
        C * Real.exp ((K - ρo) / t) ≤ Real.exp ((K - ρo / 2) / t) := by
      have hmul :=
        mul_le_mul_of_nonneg_right hCabs (Real.exp_pos ((K - ρo) / t)).le
      calc
        C * Real.exp ((K - ρo) / t)
            ≤ Real.exp ((ρo / 2) / t) * Real.exp ((K - ρo) / t) := hmul
        _ = Real.exp ((K - ρo / 2) / t) := by
          rw [← Real.exp_add]
          congr
          field_simp [htpos.ne']
          ring
    have hr0_le : r0 ≤ ρo / 2 := by
      dsimp [r0]
      exact min_le_right _ _
    have hexp_le :
        Real.exp ((K - ρo / 2) / t) ≤ Real.exp ((K - r0) / t) :=
      Real.exp_monotone <|
        div_le_div_of_nonneg_right (by linarith) htpos.le
    exact (htoC.trans htoGap).trans (habsorb.trans hexp_le)
  have hF_upper_point :
      (∑' n : ℕ, a n * Real.exp (-(t * n))) ≤ Real.exp ((K - τ) / t) := by
    have habel := laplace_eq_abel_cum a ha htpos (hsum t htpos)
    have hpre :
        (∑' n : ℕ, a n * Real.exp (-(t * n)))
          ≤ 2 * Real.exp ((K - r0) / t) := by
      calc
        (∑' n : ℕ, a n * Real.exp (-(t * n)))
            = fac * (∑' N : ℕ, full N) := by
              simpa [fac, full] using habel
        _ = fac * ((∑' N : ℕ, win N) + (∑' N : ℕ, off N)) := by
              rw [hsplit]
        _ = fac * (∑' N : ℕ, win N) + fac * (∑' N : ℕ, off N) := by
              ring
        _ ≤ Real.exp ((K - r0) / t) + Real.exp ((K - r0) / t) :=
              add_le_add hwin_part hoff_part
        _ = 2 * Real.exp ((K - r0) / t) := by ring
    have habsorb :
        2 * Real.exp ((K - r0) / t) ≤ Real.exp ((K - τ) / t) := by
      have hmul :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos ((K - r0) / t)).le
      calc
        2 * Real.exp ((K - r0) / t)
            ≤ Real.exp (τ / t) * Real.exp ((K - r0) / t) := hmul
        _ = Real.exp ((K - τ) / t) := by
          rw [← Real.exp_add]
          congr
          dsimp [τ]
          field_simp [htpos.ne']
          ring
    exact hpre.trans habsorb
  have hFpos : 0 < ∑' n : ℕ, a n * Real.exp (-(t * n)) :=
    laplace_pos_of_one_le ha ha0 (hsum t htpos)
  have hlog_lower :
      (K - τ / 2) / t ≤
        Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))) := by
    rw [div_le_iff₀ ht]
    simpa [mul_comm] using hFLower
  have hF_lower_point :
      Real.exp ((K - τ / 2) / t) ≤
        ∑' n : ℕ, a n * Real.exp (-(t * n)) :=
    (Real.le_log_iff_exp_le hFpos).mp hlog_lower
  have hstrict :
      Real.exp ((K - τ) / t) < Real.exp ((K - τ / 2) / t) :=
    Real.exp_lt_exp.mpr <|
      div_lt_div_of_pos_right (by linarith [hτ]) htpos
  exact not_lt_of_ge hF_lower_point (hF_upper_point.trans_lt hstrict)

private lemma sqrt_const_div_nat_tendsto_nhdsWithin_zero
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun M : ℕ => Real.sqrt (A / (M : ℝ))) atTop (𝓝[>] (0 : ℝ)) := by
  have harg :
      Tendsto (fun M : ℕ => A / (M : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop)
  have hnhds :
      Tendsto (fun M : ℕ => Real.sqrt (A / (M : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, Real.sqrt_zero]
      using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp harg
  have hpos : ∀ᶠ M : ℕ in atTop, 0 < Real.sqrt (A / (M : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
    exact Real.sqrt_pos.mpr (div_pos hA hMpos)
  exact tendsto_nhdsWithin_iff.mpr ⟨hnhds, hpos⟩

theorem tauberian_cum_eventual_lower
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {K : ℝ} (hK : 0 < K)
    (hsum : ∀ t > 0, Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (hF :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))))
        (𝓝[>] 0) (𝓝 K)) :
    ∀ γ > 0, ∀ᶠ M : ℕ in atTop,
      (2 * Real.sqrt K - γ) * Real.sqrt (M : ℝ) ≤ Real.log (Cum a M) := by
  intro γ hγ
  let s : ℝ := Real.sqrt K
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr hK
  let ε : ℝ := min s (γ / 4)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hs (by positivity)
  have hε_le_s : ε ≤ s := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_le_γ : ε ≤ γ / 4 := by
    dsimp [ε]
    exact min_le_right _ _
  let δ : ℝ := min (1 / 2 : ℝ) (γ / (16 * s))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (by positivity)
  have hδ_le_half : δ ≤ 1 / 2 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ1 : δ < 1 := by linarith
  have hδ_le_γ : δ ≤ γ / (16 * s) := by
    dsimp [δ]
    exact min_le_right _ _
  let r : ℝ := (1 - δ) / (1 + δ)
  have hden_pos : 0 < 1 + δ := by linarith
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (by linarith) hden_pos.le
  have hr_le_one : r ≤ 1 := by
    dsimp [r]
    rw [div_le_one hden_pos]
    linarith
  have hr_ge : 1 - 2 * δ ≤ r := by
    dsimp [r]
    rw [le_div_iff₀ hden_pos]
    nlinarith [sq_nonneg δ]
  have hsqrtr_ge_r : r ≤ Real.sqrt r := by
    rw [Real.le_sqrt hr_nonneg hr_nonneg]
    nlinarith [hr_nonneg, hr_le_one]
  have hsqrtr_ge : 1 - 2 * δ ≤ Real.sqrt r :=
    hr_ge.trans hsqrtr_ge_r
  have hδ_loss : 4 * s * δ ≤ γ / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hδ_le_γ (by positivity : 0 ≤ 4 * s)
    have hs_ne : s ≠ 0 := hs.ne'
    calc
      4 * s * δ ≤ 4 * s * (γ / (16 * s)) := by
        simpa [mul_assoc] using hmul
      _ = γ / 4 := by
        field_simp [hs_ne]
        ring
  have hcoeff_nonneg : 0 ≤ 2 * s - ε := by linarith
  have hcoef_lower :
      2 * s - γ ≤ (2 * s - ε) * Real.sqrt r := by
    have hmul :
        (2 * s - ε) * (1 - 2 * δ) ≤ (2 * s - ε) * Real.sqrt r :=
      mul_le_mul_of_nonneg_left hsqrtr_ge hcoeff_nonneg
    have hbase : 2 * s - γ ≤ (2 * s - ε) * (1 - 2 * δ) := by
      have hεδ_nonneg : 0 ≤ 2 * ε * δ := by positivity
      nlinarith [hε_le_γ, hδ_loss, hεδ_nonneg]
    exact hbase.trans hmul
  let A : ℝ := (1 + δ) * K
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos hden_pos hK
  have hlocEv :=
    tauberian_exists_large_cum_near_saddle a ha ha0 hK hsum hF hε hδ hδ1
  have htend : Tendsto (fun M : ℕ => Real.sqrt (A / (M : ℝ))) atTop (𝓝[>] (0 : ℝ)) :=
    sqrt_const_div_nat_tendsto_nhdsWithin_zero hA
  have hlocM :
      ∀ᶠ M : ℕ in atTop,
        ∃ N : ℕ,
          (1 - δ) * K / (Real.sqrt (A / (M : ℝ))) ^ 2 ≤ (N : ℝ) ∧
          (N : ℝ) ≤ (1 + δ) * K / (Real.sqrt (A / (M : ℝ))) ^ 2 ∧
          (2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) ≤ Real.log (Cum a N) :=
    htend.eventually hlocEv
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlocM] with M hM hloc
  rcases hloc with ⟨N, hNL, hNU, hNlarge⟩
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  let tM : ℝ := Real.sqrt (A / (M : ℝ))
  have htM_sq : tM ^ 2 = A / (M : ℝ) := by
    dsimp [tM]
    rw [Real.sq_sqrt (div_nonneg hA.le hMpos.le)]
  have hupper_eq : (1 + δ) * K / tM ^ 2 = (M : ℝ) := by
    rw [htM_sq]
    change A / (A / (M : ℝ)) = (M : ℝ)
    field_simp [hA.ne', hMpos.ne']
  have hlower_eq : (1 - δ) * K / tM ^ 2 = r * (M : ℝ) := by
    rw [htM_sq]
    dsimp [A, r]
    field_simp [hden_pos.ne', hK.ne', hMpos.ne']
  have hNU' : (N : ℝ) ≤ (M : ℝ) := by
    simpa [tM] using hNU.trans_eq hupper_eq
  have hNM : N ≤ M := by exact_mod_cast hNU'
  have hlower_eq' :
      (1 - δ) * K / (Real.sqrt (A / (M : ℝ))) ^ 2 = r * (M : ℝ) := by
    simpa [tM] using hlower_eq
  have hsqrtA_pos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsqrtM_pos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
  have hsqrt_div_sq :
      (Real.sqrt A / Real.sqrt (M : ℝ)) ^ 2 = A / (M : ℝ) := by
    field_simp [hsqrtM_pos.ne']
    rw [Real.sq_sqrt hA.le, Real.sq_sqrt hMpos.le]
    ring
  have hlower_eq'' :
      (1 - δ) * K / (Real.sqrt A / Real.sqrt (M : ℝ)) ^ 2 = r * (M : ℝ) := by
    rw [hsqrt_div_sq]
    dsimp [A, r]
    field_simp [hden_pos.ne', hK.ne', hMpos.ne']
  have hNL' : r * (M : ℝ) ≤ (N : ℝ) := by
    simpa [hlower_eq'', hlower_eq'] using hNL
  have hsqrt_rM_le_N : Real.sqrt (r * (M : ℝ)) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt hNL'
  have hsqrt_rM :
      Real.sqrt (r * (M : ℝ)) = Real.sqrt r * Real.sqrt (M : ℝ) := by
    rw [Real.sqrt_mul hr_nonneg]
  have hcum_mono : Cum a N ≤ Cum a M :=
    Cum_mono ha hNM
  have hlog_mono : Real.log (Cum a N) ≤ Real.log (Cum a M) :=
    Real.log_le_log (Cum_pos_of_one_le ha ha0 N) hcum_mono
  have hfrom_local :
      (2 * s - ε) * Real.sqrt (N : ℝ) ≤ Real.log (Cum a M) := by
    have hlocal' :
        (2 * s - ε) * Real.sqrt (N : ℝ) ≤ Real.log (Cum a N) := by
      simpa [s] using hNlarge
    exact hlocal'.trans hlog_mono
  calc
    (2 * Real.sqrt K - γ) * Real.sqrt (M : ℝ)
        = (2 * s - γ) * Real.sqrt (M : ℝ) := by simp [s]
    _ ≤ ((2 * s - ε) * Real.sqrt r) * Real.sqrt (M : ℝ) := by
          exact mul_le_mul_of_nonneg_right hcoef_lower (Real.sqrt_nonneg _)
    _ = (2 * s - ε) * (Real.sqrt r * Real.sqrt (M : ℝ)) := by ring
    _ = (2 * s - ε) * Real.sqrt (r * (M : ℝ)) := by rw [hsqrt_rM]
    _ ≤ (2 * s - ε) * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt_rM_le_N hcoeff_nonneg
    _ ≤ Real.log (Cum a M) := hfrom_local

theorem log_tauberian_cumulative_sqrt
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {K : ℝ} (hK : 0 < K)
    (hsum : ∀ t > 0, Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (hF :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))))
        (𝓝[>] 0) (𝓝 K)) :
    Tendsto
      (fun N : ℕ => Real.log (Cum a N) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 (2 * Real.sqrt K)) := by
  rw [Metric.tendsto_nhds]
  intro γ hγ
  have hγ2 : 0 < γ / 2 := half_pos hγ
  have hupperEv :=
    tauberian_cum_limsup a ha ha0 hK hsum hF (γ / 2) hγ2
  have hlowerEv :=
    tauberian_cum_eventual_lower a ha ha0 hK hsum hF (γ / 2) hγ2
  filter_upwards [eventually_ge_atTop (1 : ℕ), hupperEv, hlowerEv] with N hN hupper hlower
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hupper_div :
      Real.log (Cum a N) / Real.sqrt (N : ℝ) ≤ 2 * Real.sqrt K + γ / 2 := by
    rw [div_le_iff₀ hsqrtN_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hupper
  have hlower_div :
      2 * Real.sqrt K - γ / 2 ≤
        Real.log (Cum a N) / Real.sqrt (N : ℝ) := by
    rw [le_div_iff₀ hsqrtN_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlower
  have habs :
      |Real.log (Cum a N) / Real.sqrt (N : ℝ) - 2 * Real.sqrt K| < γ := by
    rw [abs_lt]
    constructor <;> linarith
  simpa [Real.dist_eq] using habs

end
end AnalyticCombinatorics.Ch8.Partitions.Tauberian

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology Asymptotics

-- The final transfer combines real logarithm/square-root limits with field
-- simplification; this keeps those terminal proofs within the local file.
set_option maxHeartbeats 400000

theorem part_zero : part 0 = 1 := by
  simp [part]

lemma addOnesPartition_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (addOnesPartition (m := m) (n := n) hmn) := by
  intro p q hpq
  apply Nat.Partition.ext
  have hparts :
      p.parts + Multiset.replicate (n - m) 1 =
        q.parts + Multiset.replicate (n - m) 1 := by
    exact congrArg Nat.Partition.parts hpq
  exact (add_left_injective (Multiset.replicate (n - m) (1 : ℕ))) hparts

theorem part_mono : Monotone part := by
  intro m n hmn
  dsimp [part]
  exact_mod_cast
    Fintype.card_le_of_injective
      (addOnesPartition (m := m) (n := n) hmn)
      (addOnesPartition_injective (m := m) (n := n) hmn)

theorem part_le_PartCum (N : ℕ) :
    part N ≤ PartCum N := by
  simpa [PartCum] using
    (Tauberian.term_le_Cum (a := part) (fun n => (part_pos n).le) N)

theorem PartCum_le_mul_part (N : ℕ) :
    PartCum N ≤ (N + 1 : ℝ) * part N := by
  unfold PartCum Tauberian.Cum
  calc
    (∑ n ∈ Finset.range (N + 1), part n)
        ≤ ∑ n ∈ Finset.range (N + 1), part N := by
          exact Finset.sum_le_sum fun n hn =>
            part_mono (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
    _ = (N + 1 : ℝ) * part N := by
          simp [Finset.sum_const, nsmul_eq_mul]

theorem partition_cum_log_asymptotic :
    Tendsto
      (fun N : ℕ => Real.log (PartCum N) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 (2 * Real.sqrt A)) := by
  have h :=
    Tauberian.log_tauberian_cumulative_sqrt
      (a := part)
      (ha := fun n => (part_pos n).le)
      (ha0 := by rw [part_zero])
      (hK := A_pos)
      (hsum := fun t ht => partLaplace_summable ht)
      (hF := by simpa [PartLaplace] using partition_laplace_log_asymptotic)
  simpa [PartCum] using h

lemma log_nat_succ_div_sqrt_tendsto_zero :
    Tendsto
      (fun N : ℕ => Real.log ((N : ℝ) + 1) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 0) := by
  have hlog_real :
      Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hsucc_atTop : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hlog_succ :
      Tendsto
        (fun N : ℕ => Real.log ((N : ℝ) + 1) / Real.sqrt ((N : ℝ) + 1))
        atTop
        (𝓝 0) :=
    hlog_real.comp hsucc_atTop
  have hratio :
      Tendsto
        (fun N : ℕ => Real.sqrt (((N : ℝ) + 1) / (N : ℝ)))
        atTop
        (𝓝 1) := by
    have hdiv :
        Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 1) := by
      simpa [mul_comm, add_comm] using
        (tendsto_add_mul_div_add_mul_atTop_nhds
          (𝕜 := ℝ) (a := 1) (b := 0) (c := 1) (d := 1) one_ne_zero)
    simpa [Real.sqrt_one] using hdiv.sqrt
  have hprod := hlog_succ.mul hratio
  simpa using
    (hprod.congr' <| by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
      have hsqrtN_ne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
      have hsqrt_succ_ne : Real.sqrt ((N : ℝ) + 1) ≠ 0 := by positivity
      have hsqrt_div :
          Real.sqrt (((N : ℝ) + 1) / (N : ℝ)) =
            Real.sqrt ((N : ℝ) + 1) / Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_div (by positivity : 0 ≤ (N : ℝ) + 1)]
      rw [hsqrt_div]
      field_simp [hsqrtN_ne, hsqrt_succ_ne])

lemma PartCum_log_part_log_gap_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        (Real.log (PartCum N) - Real.log (part N)) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    log_nat_succ_div_sqrt_tendsto_zero ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hpart_pos : 0 < part N := part_pos N
    have hcum_pos : 0 < PartCum N := hpart_pos.trans_le (part_le_PartCum N)
    have hlog_le : Real.log (part N) ≤ Real.log (PartCum N) :=
      Real.log_le_log hpart_pos (part_le_PartCum N)
    rw [div_nonneg_iff]
    exact Or.inl ⟨sub_nonneg.mpr hlog_le, hsqrtN_pos.le⟩
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hpart_pos : 0 < part N := part_pos N
    have hcum_pos : 0 < PartCum N := hpart_pos.trans_le (part_le_PartCum N)
    have hlog_upper :
        Real.log (PartCum N) ≤ Real.log ((N + 1 : ℝ) * part N) :=
      Real.log_le_log hcum_pos (PartCum_le_mul_part N)
    have hlog_mul :
        Real.log ((N + 1 : ℝ) * part N) =
          Real.log ((N : ℝ) + 1) + Real.log (part N) := by
      rw [Real.log_mul (by positivity : ((N : ℝ) + 1) ≠ 0) hpart_pos.ne']
    have hnum :
        Real.log (PartCum N) - Real.log (part N) ≤ Real.log ((N : ℝ) + 1) := by
      calc
        Real.log (PartCum N) - Real.log (part N)
            ≤ Real.log ((N + 1 : ℝ) * part N) - Real.log (part N) := by
              exact sub_le_sub_right hlog_upper _
        _ = Real.log ((N : ℝ) + 1) := by
              rw [hlog_mul]
              ring
    exact div_le_div_of_nonneg_right hnum hsqrtN_pos.le

lemma PartCum_part_log_div_gap_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        Real.log (PartCum N) / Real.sqrt (N : ℝ) -
          Real.log (part N) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 0) := by
  refine PartCum_log_part_log_gap_tendsto_zero.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrtN_ne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
  field_simp [hsqrtN_ne]

theorem two_sqrt_A_const_eq :
    2 * Real.sqrt A = Real.pi * Real.sqrt (2 / 3) := by
  simpa using two_sqrt_A_eq 1

theorem partition_log_asymptotic :
    Tendsto
      (fun n : ℕ => Real.log (part n) / Real.sqrt n)
      atTop
      (𝓝 (Real.pi * Real.sqrt (2 / 3))) := by
  have hpart_to_cum :=
    partition_cum_log_asymptotic.sub PartCum_part_log_div_gap_tendsto_zero
  have hpart :
      Tendsto
        (fun n : ℕ => Real.log (part n) / Real.sqrt (n : ℝ))
        atTop
        (𝓝 (2 * Real.sqrt A)) := by
    simpa using
      (hpart_to_cum.congr' <| by
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        ring)
  simpa [two_sqrt_A_const_eq] using hpart

lemma partition_log_target_eq_const_mul_sqrt {n : ℕ} :
    Real.pi * Real.sqrt (2 * (n : ℝ) / 3) =
      (Real.pi * Real.sqrt (2 / 3)) * Real.sqrt (n : ℝ) := by
  have harg : 2 * (n : ℝ) / 3 = (2 / 3 : ℝ) * (n : ℝ) := by ring
  rw [harg, Real.sqrt_mul (by positivity : 0 ≤ (2 / 3 : ℝ))]
  ring

end AnalyticCombinatorics.Ch8.Partitions

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions
open Filter
open scoped BigOperators Topology Asymptotics
set_option maxHeartbeats 400000
theorem solution :
    (fun n : ℕ => Real.log (part n)) ~[atTop]
      (fun n : ℕ => Real.pi * Real.sqrt (2 * (n : ℝ) / 3)) := by
  have htarget_ne :
      ∀ᶠ n : ℕ in atTop, Real.pi * Real.sqrt (2 * (n : ℝ) / 3) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    positivity
  refine (Asymptotics.isEquivalent_iff_tendsto_one htarget_ne).mpr ?_
  have hconst_pos : 0 < Real.pi * Real.sqrt (2 / 3) := by positivity
  have hratio :
      Tendsto
        (fun n : ℕ =>
          (Real.log (part n) / Real.sqrt (n : ℝ)) /
            (Real.pi * Real.sqrt (2 / 3)))
        atTop
        (𝓝 1) := by
    have h :=
      partition_log_asymptotic.div_const (Real.pi * Real.sqrt (2 / 3))
    simpa [hconst_pos.ne'] using h
  refine hratio.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
  have hconst_ne : Real.pi * Real.sqrt (2 / 3) ≠ 0 := hconst_pos.ne'
  simp only [Pi.div_apply]
  rw [partition_log_target_eq_const_mul_sqrt]
  field_simp [hsqrt_ne, hconst_ne]
