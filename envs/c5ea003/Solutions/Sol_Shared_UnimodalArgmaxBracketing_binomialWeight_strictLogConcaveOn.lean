-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.binomialWeight_strictLogConcaveOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:47:18.996369+00:00
-- url     : https://prove2.me/submissions/8956d453-5183-4135-b9c3-7431ce0fb451

-- Sol generated from Shared/UnimodalArgmaxBinomial.lean
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBinomial
import Definitions.Def_Shared_UnimodalArgmaxBracketing
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_Nat_choose_mul_choose_lt_choose_sq
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
theorem solution(hp : 0 < p) (hq : 0 < q) :
    StrictLogConcaveOn n (binomialWeight n p q) := by
  refine ⟨fun k hk => binomialWeight_pos hp hq hk, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, n = k + 2 + m := ⟨n - k - 2, by omega⟩
  have e1 : n - k = m + 2 := by omega
  have e2 : n - (k + 1) = m + 1 := by omega
  have e3 : n - (k + 2) = m := by omega
  have hchoose : (n.choose k : ℝ) * n.choose (k + 2) < (n.choose (k + 1) : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_mul_choose_lt_choose_sq hk
  have hX : (0 : ℝ) < p ^ (k + k + 2) * q ^ (m + m + 2) := by positivity
  unfold binomialWeight
  rw [e1, e2, e3]
  calc ((n.choose k : ℝ) * p ^ k * q ^ (m + 2)) * ((n.choose (k + 2) : ℝ) * p ^ (k + 2) * q ^ m)
      = ((n.choose k : ℝ) * n.choose (k + 2)) * (p ^ (k + k + 2) * q ^ (m + m + 2)) := by
        ring
    _ < ((n.choose (k + 1) : ℝ) ^ 2) * (p ^ (k + k + 2) * q ^ (m + m + 2)) :=
        mul_lt_mul_of_pos_right hchoose hX
    _ = ((n.choose (k + 1) : ℝ) * p ^ (k + 1) * q ^ (m + 1)) ^ 2 := by ring
