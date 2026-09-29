-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.binomialWeight_max_term_bracket
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:52:31.43868+00:00
-- url     : https://prove2.me/submissions/f5adbc97-d634-4c12-95f5-bf8a200f1d5a

-- Sol generated from Shared/UnimodalArgmaxBinomial.lean
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBinomial
import Definitions.Def_Shared_UnimodalArgmaxBracketing
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_ThresholdWindow_firstArgmax_eq
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_binomialWeight_strictLogConcaveOn
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_binomialWeight_thresholdWindow
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_le_value_firstArgmax
/-
# The two bracketing degrees of the binomial weights, explicitly

Companion to `Shared.UnimodalArgmaxBracketing`.  There the abstract theory was set
up: a strictly log-concave positive window `a 0, …, a n` is strictly unimodal and
its maximiser set is the interval `[firstArgmax, lastArgmax]` between the two
bracketing degrees, whose gap is `0` or `1`.

Here the abstract machine is run on the **binomial weights**

`binomialWeight n p q k = C(n,k) * p ^ k * q ^ (n - k)`  (`p, q > 0`),

the individual terms of the binomial theorem for `(p + q) ^ n`.  The output is a
completely explicit description of both bracketing degrees in terms of the single
real *mode parameter*

`modeParameter n p q = (n + 1) * p / (p + q)`.

Main results:

* `Nat.choose_mul_choose_lt_choose_sq` — strict log-concavity of a row of Pascal's
  triangle (`C(n,k) * C(n,k+2) < C(n,k+1)^2`), proved from
  `Nat.choose_succ_right_eq` alone.
* `binomialWeight_strictLogConcaveOn` — the weights form a strictly log-concave
  window.
* `binomialWeight_firstArgmax` : `d⁻ = ⌈θ⌉₊ - 1`,
  `binomialWeight_lastArgmax` : `d⁺ = ⌊θ⌋₊`.
* `binomialWeight_bracket_gap` : `d⁺ = d⁻ + 1 ↔ θ ∈ ℕ` — **the explicit comparison
  of the two bracketing degrees**.
* `binomialWeight_nat_bracket_gap` : for natural weights, the plateau occurs iff
  `(p + q) ∣ (n + 1) * p`.
* `choose_firstArgmax`, `choose_lastArgmax`, `choose_bracket_gap` : for `p = q = 1`
  the degrees are `n / 2` and `(n + 1) / 2`, and the plateau occurs iff `n` is odd.
* `binomialWeight_max_term_bracket` : the largest term of the binomial expansion is
  squeezed between `(p+q)^n / (n+1)` and `(p+q)^n`.
-/

open Shared
open UnimodalArgmaxBracketing

/-! ## Strict log-concavity of a row of Pascal's triangle -/


/-! ## The binomial weights -/



variable {n : ℕ} {p q : ℝ}

theorem binomialWeight_pos (hp : 0 < p) (hq : 0 < q) {k : ℕ} (hk : k ≤ n) :
    0 < binomialWeight n p q k := by
  have : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  unfold binomialWeight
  positivity


theorem modeParameter_lt (hp : 0 < p) (hq : 0 < q) : modeParameter n p q < (n : ℝ) + 1 := by
  unfold modeParameter
  have hpq : (0 : ℝ) < p + q := by linarith
  rw [div_lt_iff₀ hpq]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]


/-! ## The rise criterion -/




/-! ## The two bracketing degrees, explicitly -/


/-- **The lower bracketing degree of the binomial weights is `⌈θ⌉₊ - 1`.** -/
theorem binomialWeight_firstArgmax (hp : 0 < p) (hq : 0 < q) :
    firstArgmax n (binomialWeight n p q) = ⌈modeParameter n p q⌉₊ - 1 :=
  (binomialWeight_thresholdWindow hp hq).firstArgmax_eq


/-! ## The explicit comparison of the two bracketing degrees -/



/-! ## Dependence of the brackets on the parameters -/






/-- Every binomial weight is dominated by the weight at the lower bracketing degree. -/
theorem binomialWeight_le_max (hp : 0 < p) (hq : 0 < q) {k : ℕ} (hk : k ≤ n) :
    binomialWeight n p q k ≤ binomialWeight n p q (⌈modeParameter n p q⌉₊ - 1) := by
  have h := le_value_firstArgmax (binomialWeight_strictLogConcaveOn hp hq) hk
  rwa [binomialWeight_firstArgmax hp hq] at h

/-! ## Arithmetic form of the comparison, and the classical case `p = q = 1` -/








/-! ## The largest term of the binomial expansion -/


/-! ## Every degree is a Newton-polygon vertex

Strict log-concavity says that the points `(k, log C(n,k))` are in *strictly convex
position*.  Equivalently: after tilting by a suitable weight `p^k` every single
degree `d ≤ n` becomes the **unique** maximiser.  This is the sweep of the argmax as
the threshold `θ` runs through `(0, n+1)`. -/



open Shared in
theorem solution(hp : 0 < p) (hq : 0 < q) :
    (p + q) ^ n / ((n : ℝ) + 1) ≤ binomialWeight n p q (⌈modeParameter n p q⌉₊ - 1) ∧
      binomialWeight n p q (⌈modeParameter n p q⌉₊ - 1) ≤ (p + q) ^ n := by
  set d := ⌈modeParameter n p q⌉₊ - 1 with hd
  have hexp : (p + q) ^ n = ∑ k ∈ Finset.range (n + 1), binomialWeight n p q k := by
    rw [add_pow]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold binomialWeight
    ring
  have hle : ∀ k ∈ Finset.range (n + 1), binomialWeight n p q k ≤ binomialWeight n p q d := by
    intro k hk
    exact binomialWeight_le_max hp hq (by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk)
  have hsum : (p + q) ^ n ≤ ((n : ℝ) + 1) * binomialWeight n p q d := by
    rw [hexp]
    calc ∑ k ∈ Finset.range (n + 1), binomialWeight n p q k
        ≤ ∑ _k ∈ Finset.range (n + 1), binomialWeight n p q d := Finset.sum_le_sum hle
      _ = ((n : ℝ) + 1) * binomialWeight n p q d := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  constructor
  · rw [div_le_iff₀ hn1]; linarith
  · have hdn : d ≤ n := by
      have hceille : ⌈modeParameter n p q⌉₊ ≤ n + 1 := by
        apply Nat.ceil_le.2
        push_cast
        linarith [modeParameter_lt (n := n) hp hq]
      omega
    have hmem : d ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    rw [hexp]
    refine Finset.single_le_sum (fun k hk => ?_) hmem
    exact (binomialWeight_pos hp hq (by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk)).le
