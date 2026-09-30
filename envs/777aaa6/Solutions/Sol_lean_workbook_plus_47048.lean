-- Prove2me | solution 1 for lean_workbook_plus_47048
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:21:46.38633+00:00
-- url     : https://prove2.me/submissions/180cf90c-c26c-4f78-9351-5b74369b8761

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset Filter Topology

theorem one_add_sum_le_product {ι : Type*} (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (s : Finset ι) : 1 + ∑ i ∈ s, b i ≤ ∏ i ∈ s, (1 + b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have hs : 0 ≤ ∑ i ∈ s, b i := sum_nonneg fun i _ => hb i
    have hmul := mul_nonneg (hb a) hs
    have ht := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1 + b a by linarith [hb a])
    nlinarith

theorem nonnegative_one_add_multipliable_iff {ι : Type*} (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) : Multipliable (fun i => 1 + b i) ↔ Summable b := by
  classical
  constructor
  · intro h
    obtain ⟨C, hC, s, hs⟩ := h.eventually_bounded_finset_prod
    apply summable_of_sum_le hb
    intro t
    calc
      ∑ i ∈ t, b i ≤ ∑ i ∈ t ∪ s, b i :=
        sum_le_sum_of_subset_of_nonneg subset_union_left (fun i _ _ => hb i)
      _ ≤ ∏ i ∈ t ∪ s, (1 + b i) := by
        linarith [one_add_sum_le_product b hb (t ∪ s)]
      _ ≤ C := hs (t ∪ s) subset_union_right
  · exact Real.multipliable_one_add_of_summable

theorem nonnegative_product_log_formula {ι : Type*} (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hs : Summable b) :
    (∏' i, (1 + b i)) = Real.exp (∑' i, Real.log (1 + b i)) := by
  exact (Real.rexp_tsum_eq_tprod (fun i => by linarith [hb i])
    (Real.summable_log_one_add_of_summable hs)).symm

theorem nonnegative_product_bounds {ι : Type*} (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hs : Summable b) :
    1 + ∑' i, b i ≤ ∏' i, (1 + b i) ∧
    (∏' i, (1 + b i)) ≤ Real.exp (∑' i, b i) := by
  have hp := (nonnegative_one_add_multipliable_iff b hb).mpr hs
  constructor
  · exact le_of_tendsto_of_tendsto (tendsto_const_nhds.add hs.hasSum) hp.hasProd
      (Filter.Eventually.of_forall (one_add_sum_le_product b hb))
  · rw [nonnegative_product_log_formula b hb hs]
    apply Real.exp_le_exp.mpr
    apply (Real.summable_log_one_add_of_summable hs).tsum_le_tsum _ hs
    intro i
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + b i by linarith [hb i])
    linarith

theorem nonnegative_product_strict_upper {ι : Type*} (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hs : Summable b) (i : ι) (hi : 0 < b i) :
    (∏' j, (1 + b j)) < Real.exp (∑' j, b j) := by
  rw [nonnegative_product_log_formula b hb hs]
  apply Real.exp_lt_exp.mpr
  apply (Real.summable_log_one_add_of_summable hs).tsum_lt_tsum (g := b) (i := i) _ _ hs
  · intro j
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + b j by linarith [hb j])
    linarith
  · have h := Real.log_lt_sub_one_of_pos (show 0 < 1 + b i by linarith)
      (show 1 + b i ≠ 1 by linarith)
    linarith

theorem nonnegative_product_relative_tail (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hs : Summable b) (N : ℕ) :
    0 ≤ (∏' n, (1 + b n)) / (∏ n ∈ range N, (1 + b n)) - 1 ∧
    (∏' n, (1 + b n)) / (∏ n ∈ range N, (1 + b n)) - 1 ≤
      Real.exp (∑' n, b (n + N)) - 1 := by
  have htail : Summable (fun n => b (n + N)) := (summable_nat_add_iff N).mpr hs
  have hptail := (nonnegative_one_add_multipliable_iff (fun n => b (n + N))
    (fun n => hb (n + N))).mpr htail
  have hfactor : (∏ n ∈ range N, (1 + b n)) * (∏' n, (1 + b (n + N))) =
      ∏' n, (1 + b n) :=
    Multipliable.prod_mul_tprod_nat_mul' (f := fun n : ℕ => 1 + b n) (k := N) hptail
  have hprefix : 0 < ∏ n ∈ range N, (1 + b n) :=
    prod_pos fun n _ => by linarith [hb n]
  have hratio : (∏' n, (1 + b n)) / (∏ n ∈ range N, (1 + b n)) =
      ∏' n, (1 + b (n + N)) := by
    apply (div_eq_iff hprefix.ne').mpr
    simpa only [mul_comm] using hfactor.symm
  rw [hratio]
  have hbounds := nonnegative_product_bounds (fun n => b (n + N))
    (fun n => hb (n + N)) htail
  have hsum : 0 ≤ ∑' n, b (n + N) := tsum_nonneg (fun n => hb (n + N))
  constructor <;> linarith

noncomputable def geometricProduct (q : ℝ) : ℝ := ∏' n : ℕ, (1 + q ^ (n + 1))

theorem geometric_power_tail_hasSum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    HasSum (fun n : ℕ => q ^ (n + N + 1)) (q ^ (N + 1) / (1 - q)) := by
  have hq : |q| < 1 := by rwa [abs_of_nonneg hq0]
  have h := (hasSum_geometric_of_abs_lt_one hq).mul_left (q ^ (N + 1))
  have heq (n : ℕ) : q ^ (n + N + 1) = q ^ (N + 1) * q ^ n := by
    rw [← pow_add]
    congr 1
    omega
  simpa only [div_eq_mul_inv] using h.congr_fun heq

theorem geometric_product_hasProd (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasProd (fun n : ℕ => 1 + q ^ (n + 1)) (geometricProduct q) := by
  have hs : Summable (fun n : ℕ => q ^ (n + 1)) := by
    simpa only [Nat.add_zero] using (geometric_power_tail_hasSum q hq0 hq1 0).summable
  exact (Real.multipliable_one_add_of_summable hs).hasProd

theorem geometric_product_partial_tendsto (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun N : ℕ => ∏ n ∈ range N, (1 + q ^ (n + 1))) atTop
      (𝓝 (geometricProduct q)) :=
  (geometric_product_hasProd q hq0 hq1).tendsto_prod_nat

theorem geometric_product_bounds (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 + q / (1 - q) ≤ geometricProduct q ∧
      geometricProduct q ≤ Real.exp (q / (1 - q)) := by
  have hs : HasSum (fun n : ℕ => q ^ (n + 1)) (q / (1 - q)) := by
    simpa only [Nat.add_zero, zero_add, pow_one] using geometric_power_tail_hasSum q hq0 hq1 0
  simpa only [geometricProduct, hs.tsum_eq] using
    nonnegative_product_bounds (fun n : ℕ => q ^ (n + 1))
      (fun n => pow_nonneg hq0 _) hs.summable

theorem geometric_product_relative_tail (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    0 ≤ geometricProduct q / (∏ n ∈ range N, (1 + q ^ (n + 1))) - 1 ∧
    geometricProduct q / (∏ n ∈ range N, (1 + q ^ (n + 1))) - 1 ≤
      Real.exp (q ^ (N + 1) / (1 - q)) - 1 := by
  have hs : Summable (fun n : ℕ => q ^ (n + 1)) := by
    simpa only [Nat.add_zero] using (geometric_power_tail_hasSum q hq0 hq1 0).summable
  simpa only [geometricProduct, (geometric_power_tail_hasSum q hq0 hq1 N).tsum_eq] using
    nonnegative_product_relative_tail (fun n : ℕ => q ^ (n + 1))
      (fun n => pow_nonneg hq0 _) hs N

theorem geometric_half_product_bounds : 2 ≤ geometricProduct (1 / 2) ∧
    geometricProduct (1 / 2) < Real.exp 1 := by
  have hs : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
    convert geometric_power_tail_hasSum (1 / 2) (by norm_num) (by norm_num) 0 using 1
    norm_num
  constructor
  · have h := (geometric_product_bounds (1 / 2) (by norm_num) (by norm_num)).1
    convert h using 1
    ring
  · simpa only [geometricProduct, hs.tsum_eq] using
      nonnegative_product_strict_upper (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1))
        (fun n => by positivity) hs.summable 0 (by norm_num)

theorem half_product_source_hasProd :
    HasProd (fun n : ℕ => 1 + (1 : ℝ) / 2 ^ (n + 1)) (geometricProduct (1 / 2)) := by
  simpa only [one_div, inv_pow] using geometric_product_hasProd (1 / 2) (by norm_num) (by norm_num)

theorem half_product_posted_hasProd :
    HasProd (fun n : ℕ => 1 + (1 : ℝ) / 2 ^ n) (2 * geometricProduct (1 / 2)) := by
  simpa only [prod_range_one, pow_zero, div_one, one_add_one_eq_two] using
    HasProd.prod_range_mul (f := fun n : ℕ => 1 + (1 : ℝ) / 2 ^ n)
      (k := 1) half_product_source_hasProd

theorem solution : ∃ a, ∏' n : ℕ, (1 + (1 : ℝ) / 2 ^ n) = a := by
  exact ⟨2 * geometricProduct (1 / 2), half_product_posted_hasProd.tprod_eq⟩

#print axioms one_add_sum_le_product
#print axioms nonnegative_one_add_multipliable_iff
#print axioms nonnegative_product_log_formula
#print axioms nonnegative_product_bounds
#print axioms nonnegative_product_strict_upper
#print axioms nonnegative_product_relative_tail
#print axioms geometricProduct
#print axioms geometric_power_tail_hasSum
#print axioms geometric_product_hasProd
#print axioms geometric_product_partial_tendsto
#print axioms geometric_product_bounds
#print axioms geometric_product_relative_tail
#print axioms geometric_half_product_bounds
#print axioms half_product_source_hasProd
#print axioms half_product_posted_hasProd
#print axioms solution
