-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.binomialWeight_lt_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T21:19:12.721644+00:00
-- url     : https://prove2.me/submissions/0d5375fe-b0ef-4bf7-bd62-e6bc9ce1ae56

-- Sol generated from Shared/UnimodalArgmaxBinomial.lean
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBinomial
import Definitions.Def_Shared_UnimodalArgmaxBracketing
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
theorem solution(hp : 0 < p) (hq : 0 < q) {k : ℕ} (hk : k < n) :
    binomialWeight n p q k < binomialWeight n p q (k + 1) ↔
      ((k : ℝ) + 1) < modeParameter n p q := by
  obtain ⟨m, hm⟩ : ∃ m, n = k + 1 + m := ⟨n - k - 1, by omega⟩
  have e1 : n - k = m + 1 := by omega
  have e2 : n - (k + 1) = m := by omega
  have hA : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (by omega)
  have key : ((n.choose (k + 1) : ℝ)) * ((k : ℝ) + 1) = (n.choose k : ℝ) * ((m : ℝ) + 1) := by
    have : n.choose (k + 1) * (k + 1) = n.choose k * (m + 1) := by
      rw [Nat.choose_succ_right_eq, e1]
    exact_mod_cast this
  have hpow : (0 : ℝ) < p ^ k * q ^ m := by positivity
  have hpq : (0 : ℝ) < p + q := by linarith
  have hstep : binomialWeight n p q k < binomialWeight n p q (k + 1) ↔
      (n.choose k : ℝ) * q < (n.choose (k + 1) : ℝ) * p := by
    unfold binomialWeight
    rw [e1, e2, show ((n.choose k : ℝ) * p ^ k * q ^ (m + 1))
          = ((n.choose k : ℝ) * q) * (p ^ k * q ^ m) from by ring,
        show ((n.choose (k + 1) : ℝ) * p ^ (k + 1) * q ^ m)
          = ((n.choose (k + 1) : ℝ) * p) * (p ^ k * q ^ m) from by ring,
        mul_lt_mul_iff_of_pos_right hpow]
  have hcross : ((n.choose k : ℝ) * q < (n.choose (k + 1) : ℝ) * p) ↔
      q * ((k : ℝ) + 1) < ((m : ℝ) + 1) * p := by
    have h1 : (n.choose k : ℝ) * (q * ((k : ℝ) + 1))
        = ((n.choose k : ℝ) * q) * ((k : ℝ) + 1) := by ring
    have h2 : (n.choose k : ℝ) * (((m : ℝ) + 1) * p)
        = ((n.choose (k + 1) : ℝ) * p) * ((k : ℝ) + 1) := by
      rw [show ((n.choose (k + 1) : ℝ) * p) * ((k : ℝ) + 1)
          = ((n.choose (k + 1) : ℝ) * ((k : ℝ) + 1)) * p from by ring, key]; ring
    constructor
    · intro h
      have h3 : (n.choose k : ℝ) * (q * ((k : ℝ) + 1))
          < (n.choose k : ℝ) * (((m : ℝ) + 1) * p) := by
        rw [h1, h2]; exact mul_lt_mul_of_pos_right h (by positivity : (0:ℝ) < (k : ℝ) + 1)
      exact lt_of_mul_lt_mul_left h3 hA.le
    · intro h
      have h3 : (n.choose k : ℝ) * (q * ((k : ℝ) + 1))
          < (n.choose k : ℝ) * (((m : ℝ) + 1) * p) := mul_lt_mul_of_pos_left h hA
      rw [h1, h2] at h3
      exact lt_of_mul_lt_mul_right h3 (by positivity : (0:ℝ) ≤ (k : ℝ) + 1)
  rw [hstep, hcross, modeParameter, lt_div_iff₀ hpq]
  have hn : (n : ℝ) = (k : ℝ) + 1 + (m : ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hm
  constructor
  · intro h; rw [hn]; nlinarith
  · intro h; rw [hn] at h; nlinarith
