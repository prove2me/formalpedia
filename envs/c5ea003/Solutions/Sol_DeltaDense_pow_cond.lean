-- Prove2me | solution 1 for DeltaDense.pow_cond
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:28:04.84079+00:00
-- url     : https://prove2.me/submissions/37db08cd-f040-4047-93d6-5537e56fadf4

-- Sol generated from Bridges/DeltaDenseSumsetAvoidance.lean
import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
/-
# δ-dense sets avoiding large arithmetic sumsets

This file develops, from scratch, a rigorous finitary construction related to the
sharpness of "sumset in a dense set" theorems (Kra–Moreira–Richter–Robertson type
statements, whose finitary form predicts that a set `S ⊆ [n]` of density `δ` should
contain a sumset `A + B` with `min(|A|,|B|) ≍ log n / log (1/δ)`).

The content here is the *sharpness* side.  For every `0 < δ < 1` and every sufficiently
large `n` we construct a set `S ⊆ [n]` with `|S| ≥ δ n` such that

* `S` contains **no** arithmetic progression of length `(5/2)·log n / log (1/δ)`
  (`DeltaDense.exists_dense_no_ap`),
* `S` contains **no** sumset `A + B` with `A` an arbitrary nonempty finite set and `B` an
  arithmetic progression of length at least `(5/2)·log n / log (1/δ)`
  (`DeltaDense.exists_dense_no_sumset_with_ap`), and
* `S` contains **no** sumset `A + B` where `A` and `B` are arithmetic progressions —
  with *arbitrary, possibly different* positive common differences — of common length
  `k ≥ 3 log n / log (1/δ)`
  (`DeltaDense.exists_dense_avoiding_ap_sumsets`, and its asymptotic packaging
  `DeltaDense.eventually_exists_dense_avoiding_ap_sumsets`).

The second statement realises the constant `C(δ) = 3` from the conjectural picture: `3`
is exactly the number of parameters `(t, d₁, d₂)` needed to describe the "L-shaped"
witness `{t, t+d₁, …, t+(k-1)d₁} ∪ {t+(k-1)d₁, …, t+(k-1)d₁+(k-1)d₂}` of `2k-1` elements
that any such sumset must contain, so the first-moment union bound costs `n³`.

The proof is a purely counting ("derandomised probabilistic method") argument over the
family of `m`-element subsets of `[n]`:

* `DeltaDense.choose_ratio_sub` : `C(n-L, m-L) · n^L ≤ C(n,m) · m^L`, the integer form of
  the estimate `P(fixed L-set ⊆ random m-subset) ≤ (m/n)^L`;
* `DeltaDense.card_filter_superset` : the number of `m`-subsets of `[n]` containing a
  fixed `L`-set is `C(n-L, m-L)`;
* `DeltaDense.exists_card_eq_avoiding_family` : the general first-moment principle — if a
  family of `|I|` sets, each of size at least `L`, satisfies `|I|·m^L < n^L`, then some
  `m`-element subset of `[n]` contains none of them;
* `DeltaDense.pow_cond` : the analytic verification of `n^c·m^L < n^L` for `m = ⌈δn⌉`.
-/

open DeltaDense

open Finset Pointwise

/-! ## Arithmetic progressions as finsets -/










/-! ## The counting estimates -/




/-! ## The general first-moment principle -/


/-! ## Progression-free and grid-free dense sets, in integer form -/



/-! ## The analytic form of the counting condition -/


/-! ## Dense sets with no long progressions and no progression sumsets -/







open DeltaDense in
theorem solution(δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) (n : ℕ) (hn2 : 2 ≤ n)
    (hδn : 1 ≤ δ * n) (hbig : 100 ≤ δ * n * Real.log (1 / δ)) (c : ℕ) (hc : c ≤ 10)
    (L : ℕ) (hL : ((c : ℝ) + 1 / 2) * (Real.log n / Real.log (1 / δ)) ≤ L) :
    n ^ c * (⌈δ * (n : ℝ)⌉₊) ^ L < n ^ L := by
  set l : ℝ := Real.log (1 / δ) with hl
  have hlpos : 0 < l := by
    rw [hl]; simp only [one_div]
    exact Real.log_pos (by rw [lt_inv_comm₀ (by norm_num) h0]; simpa using h1)
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hcR : (c : ℝ) ≤ 10 := by exact_mod_cast hc
  set m : ℕ := ⌈δ * (n : ℝ)⌉₊ with hm
  have hm1 : 1 ≤ m := by
    rw [hm]; exact Nat.one_le_ceil_iff.2 (by linarith)
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmlt : (m : ℝ) < δ * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlogm : Real.log m ≤ Real.log n - (99 / 100) * l := by
    have step1 : Real.log m ≤ Real.log (δ * n + 1) :=
      Real.log_le_log (by linarith) (le_of_lt hmlt)
    have hfac : δ * (n : ℝ) + 1 = (δ * n) * (1 + 1 / (δ * n)) := by field_simp
    have step2 : Real.log (δ * n + 1) = Real.log (δ * n) + Real.log (1 + 1 / (δ * n)) := by
      rw [hfac, Real.log_mul (by positivity) (by positivity)]
    have step3 : Real.log (1 + 1 / (δ * n)) ≤ 1 / (δ * n) := by
      have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (δ * n)) (by positivity)
      linarith
    have step4 : Real.log (δ * n) = Real.log n - l := by
      rw [Real.log_mul (ne_of_gt h0) (ne_of_gt hn0), hl]
      simp only [one_div, Real.log_inv]
      ring
    have step5 : 1 / (δ * (n : ℝ)) ≤ l / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hbig]
    linarith
  have hkey : (c : ℝ) * Real.log n + (L : ℝ) * Real.log m < (L : ℝ) * Real.log n := by
    have hLpos : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
    have h6 : (L : ℝ) * Real.log m ≤ (L : ℝ) * (Real.log n - (99 / 100) * l) :=
      mul_le_mul_of_nonneg_left hlogm hLpos
    have h7 : ((c : ℝ) + 1 / 2) * Real.log n ≤ (L : ℝ) * l := by
      refine (div_le_iff₀ hlpos).1 ?_
      calc ((c : ℝ) + 1 / 2) * Real.log n / l
          = ((c : ℝ) + 1 / 2) * (Real.log n / l) := by ring
        _ ≤ (L : ℝ) := hL
    nlinarith [h6, h7, hlogn, hcR]
  have hreal : (n : ℝ) ^ c * (m : ℝ) ^ L < (n : ℝ) ^ L := by
    have hx : (0 : ℝ) < (n : ℝ) ^ c * (m : ℝ) ^ L := by positivity
    have hy : (0 : ℝ) < (n : ℝ) ^ L := by positivity
    rw [← Real.log_lt_log_iff hx hy,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    linarith [hkey]
  exact_mod_cast hreal
