-- Prove2me | solution 1 for TruthFractalDimension.tendsto_dimEstimate_truthSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:13:12.266321+00:00
-- url     : https://prove2.me/submissions/e8f0897a-80c1-4790-a407-137c373481f7

-- Sol generated from Novelty/TruthFractalDimension.lean
import Mathlib
import Definitions.Def_Novelty_TruthFractalDimension

/-!
# The Fractal Dimension of the Space of True Statements

This file develops a rigorous, quantitative notion of *how large the set of true
statements is* inside the space of all statements, and shows that — for a natural
model — this size is a genuine fractal (box-counting) dimension lying strictly
between `0` and `1`.

## The model

We encode statements as finite binary strings.  A string of length `n` is a
function `Fin n → Bool`, and there are exactly `2 ^ n` of them.  A **theory**
`T` is an assignment, to each length `n`, of the finite set of accepted strings
of that length; its **counting function** is `count T n = (T n).card`.

The metric picture behind the definitions is the standard one on the Cantor
space of infinite binary sequences: two sequences are close when they agree on a
long common prefix.  Covering a set by cylinders of depth `n` costs one cylinder
per accepted length-`n` prefix, so the natural covering number at scale
`2^{-n}` is `count T n`.  The **box-counting dimension** is therefore

  `boxDim T = limsup_n  log₂ (count T n) / n`.

## Main results

* `boxDim_le_one` / `dimEstimate_nonneg`: every theory has dimension in `[0,1]`.
* `boxDim_allStatements`: the full space has dimension `1`.
* `boxDim_of_bounded` and `boxDim_trivialTheory`: theories with boundedly many
  statements per length are dimension `0` — negligible.
* `boxDim_truthSet`: an explicitly constructed "half-information" theory has
  dimension **exactly `1/2`**, and `truthSet_dimension_strictly_between` records
  that `0 < 1/2 < 1`: the set of true statements is *sparse but not negligible*.
* `boxDim_of_tendsto`: whenever the finite-scale estimates converge, the
  dimension equals their limit — the dimension is *approximable* from finite data.

## The link with Chaitin's constant

The concluding section models the halting probability `Ω` as a left-computable
real: the limit of an increasing sequence of finite rational approximations.
`omegaApprox_mono` and `omegaApprox_tendsto` establish exactly this
approximation-from-below, mirroring the way the box dimension is approached from
finite data; `omega_mem_unitInterval` places `Ω` in `[0,1]`, the same interval in
which every fractal dimension of truth lives.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): "truth" carved out of the space of all statements is
neither full nor vanishing; its box-counting dimension is a real number strictly
inside `(0,1)`, and it is approximable but not obviously computable, echoing
Chaitin's Ω.

Experiment (Experimenter): We built the counting/dimension machinery over
`Fin n → Bool`, proved the universal bounds, computed the full-space dimension
(`1`) and the dimension of bounded theories (`0`), and constructed an explicit
"odd coordinates must be false" theory whose count is `2^{⌈n/2⌉}`, giving
dimension `1/2`.  The precise count uses a product/`piFinset` identity; the
`1/2` limit uses the exact parity count `2·⌈n/2⌉ = n + [n odd]` and a squeeze.

Analysis (Analyst): The value `1/2` is forced by the linear density of free
coordinates; any fixed rational density `p/q` of free coordinates would yield
dimension `p/q`, so every value in `[0,1] ∩ ℚ` is realized.  The `limsup`
definition is essential: for irregular theories the finite estimates need not
converge, and only the `limsup` is stable.

Critique (Critic): Dimension `1/2` is not a definitional triviality — it rests on
the exact combinatorial count and a genuine analytic squeeze.  We avoided the
vacuous route (`native_decide` on a fixed `n`) by proving the count for *all* `n`.
The Ω section is deliberately modest: we prove approximability-from-below
rigorously and do *not* assert uncomputability, which needs the full theory of
computable reals; that is flagged as a future direction.

Synthesis (PI): Truth, measured by covering the Cantor space of statements, has a
fractal dimension in the open unit interval; that dimension is the limit of
finite, effectively-computable estimates, exactly as Ω is the limit of finite
lower bounds.
-/

open Filter Topology

open TruthFractalDimension





/-! ### Universal bounds: every dimension lies in `[0,1]` -/







/-! ### The full space has dimension `1` -/






/-! ### Bounded theories are negligible (dimension `0`) -/







/-! ### The set of true statements: dimension exactly `1/2` -/




theorem count_truthSet (n : ℕ) : count truthSet n = 2 ^ (evenCount n) := by
  unfold count truthSet evenCount
  rw [Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_univ, Fintype.card_bool]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 2
  apply Finset.filter_congr
  intro i _; simp [Nat.not_odd_iff_even]

/-- Exact parity count: `2 · (#evens below n) = n + [n odd]`. -/
theorem two_mul_sumEven_exact (n : ℕ) :
    2 * (∑ k ∈ Finset.range n, (if Even k then 1 else 0)) = n + (if Even n then 0 else 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    rcases Nat.even_or_odd m with hk | hk
    · rw [if_pos hk, if_pos hk, if_neg (by simp [Nat.even_add_one, hk])]
    · rw [if_neg (by simpa [Nat.not_even_iff_odd] using hk),
          if_neg (by simpa [Nat.not_even_iff_odd] using hk),
          if_pos (by simp [Nat.even_add_one]; simpa [Nat.not_even_iff_odd] using hk)]

theorem evenCount_eq_sum (n : ℕ) :
    evenCount n = ∑ k ∈ Finset.range n, (if Even k then 1 else 0) := by
  unfold evenCount
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun k => if Even k then 1 else 0)]

theorem evenCount_bound (n : ℕ) : n ≤ 2 * evenCount n ∧ 2 * evenCount n ≤ n + 1 := by
  rw [evenCount_eq_sum, two_mul_sumEven_exact]
  rcases Nat.even_or_odd n with h | h
  · simp [h]
  · rw [if_neg (by simpa [Nat.not_even_iff_odd] using h)]; omega

theorem dimEstimate_truthSet (n : ℕ) : dimEstimate truthSet n = (evenCount n : ℝ) / n := by
  unfold dimEstimate
  rw [count_truthSet]
  have h : Real.logb 2 (((2 : ℕ) ^ (evenCount n) : ℕ) : ℝ) = evenCount n := by
    push_cast; rw [Real.logb_pow]; simp
  rw [h]




/-! ### Approximability of the dimension from finite data -/


/-! ### Link with Chaitin's constant `Ω`: approximability from below -/















open TruthFractalDimension in
theorem solution:
    Filter.Tendsto (dimEstimate truthSet) Filter.atTop (nhds (1 / 2)) := by
  have hup : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (2 * n)) Filter.atTop (nhds (1 / 2)) := by
    have hEq : (fun n : ℕ => ((n : ℝ) + 1) / (2 * n))
        =ᶠ[Filter.atTop] (fun n : ℕ => 1 / 2 + 1 / (2 * n)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    rw [tendsto_congr' hEq]
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) Filter.atTop (nhds 0) := by
      have h := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
      simp only [mul_zero] at h
      exact h.congr (fun n => by ring)
    simpa using tendsto_const_nhds.add h0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [dimEstimate_truthSet, div_le_div_iff₀ (by norm_num) (by exact_mod_cast hn)]
    have hb : (n : ℝ) ≤ 2 * evenCount n := by exact_mod_cast (evenCount_bound n).1
    nlinarith [hb]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [dimEstimate_truthSet, div_le_div_iff₀ (by exact_mod_cast hn) (by positivity)]
    have hb : (2 : ℝ) * evenCount n ≤ (n : ℝ) + 1 := by exact_mod_cast (evenCount_bound n).2
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith [hb, hn0]
