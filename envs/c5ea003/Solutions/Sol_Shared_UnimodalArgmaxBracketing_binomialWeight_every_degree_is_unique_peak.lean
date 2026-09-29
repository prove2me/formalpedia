-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.binomialWeight_every_degree_is_unique_peak
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:50:23.376505+00:00
-- url     : https://prove2.me/submissions/3af7fe15-170a-4da6-829e-681cda849385

-- Sol generated from Shared/UnimodalArgmaxBinomial.lean
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBinomial
import Definitions.Def_Shared_UnimodalArgmaxBracketing
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_ThresholdWindow_firstArgmax_eq
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_ThresholdWindow_lastArgmax_eq
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_binomialWeight_strictLogConcaveOn
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_binomialWeight_thresholdWindow
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_lt_value_firstArgmax_of_outside
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





/-! ## The rise criterion -/




/-! ## The two bracketing degrees, explicitly -/


/-- **The lower bracketing degree of the binomial weights is `⌈θ⌉₊ - 1`.** -/
theorem binomialWeight_firstArgmax (hp : 0 < p) (hq : 0 < q) :
    firstArgmax n (binomialWeight n p q) = ⌈modeParameter n p q⌉₊ - 1 :=
  (binomialWeight_thresholdWindow hp hq).firstArgmax_eq

/-- **The upper bracketing degree of the binomial weights is `⌊θ⌋₊`.** -/
theorem binomialWeight_lastArgmax (hp : 0 < p) (hq : 0 < q) :
    lastArgmax n (binomialWeight n p q) = ⌊modeParameter n p q⌋₊ :=
  (binomialWeight_thresholdWindow hp hq).lastArgmax_eq

/-! ## The explicit comparison of the two bracketing degrees -/



/-! ## Dependence of the brackets on the parameters -/







/-! ## Arithmetic form of the comparison, and the classical case `p = q = 1` -/








/-! ## The largest term of the binomial expansion -/


/-! ## Every degree is a Newton-polygon vertex

Strict log-concavity says that the points `(k, log C(n,k))` are in *strictly convex
position*.  Equivalently: after tilting by a suitable weight `p^k` every single
degree `d ≤ n` becomes the **unique** maximiser.  This is the sweep of the argmax as
the threshold `θ` runs through `(0, n+1)`. -/



open Shared in
theorem solution(n d : ℕ) (hd : d ≤ n) :
    ∃ p : ℝ, 0 < p ∧ ∀ k ≤ n, k ≠ d →
      binomialWeight n p 1 k < binomialWeight n p 1 d := by
  set θ : ℝ := (d : ℝ) + 1 / 2 with hθdef
  have hθpos : 0 < θ := by positivity
  have hdn : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hd
  have hθlt : θ < (n : ℝ) + 1 := by rw [hθdef]; linarith
  have hden : (0 : ℝ) < ((n : ℝ) + 1) - θ := by linarith
  refine ⟨θ / (((n : ℝ) + 1) - θ), by positivity, ?_⟩
  set p : ℝ := θ / (((n : ℝ) + 1) - θ) with hpdef
  have hp : 0 < p := by rw [hpdef]; positivity
  have hmode : modeParameter n p 1 = θ := by
    have hsum : p + 1 = ((n : ℝ) + 1) / (((n : ℝ) + 1) - θ) := by
      rw [hpdef]; field_simp; ring
    rw [modeParameter, hsum, hpdef]
    field_simp
  have hceil : ⌈θ⌉₊ = d + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [hθdef]
    push_cast
    constructor <;> linarith
  have hfloor : ⌊θ⌋₊ = d := by
    rw [Nat.floor_eq_iff (by positivity), hθdef]
    constructor <;> linarith
  have hfirst : firstArgmax n (binomialWeight n p 1) = d := by
    rw [binomialWeight_firstArgmax hp one_pos, hmode, hceil]
    omega
  have hlast : lastArgmax n (binomialWeight n p 1) = d := by
    rw [binomialWeight_lastArgmax hp one_pos, hmode, hfloor]
  intro k hk hkd
  have hout : k < firstArgmax n (binomialWeight n p 1) ∨
      lastArgmax n (binomialWeight n p 1) < k := by
    rw [hfirst, hlast]
    omega
  have := lt_value_firstArgmax_of_outside (binomialWeight_strictLogConcaveOn hp one_pos) hk hout
  rwa [hfirst] at this
