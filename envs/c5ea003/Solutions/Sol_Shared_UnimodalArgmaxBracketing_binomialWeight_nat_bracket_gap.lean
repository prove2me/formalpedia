-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.binomialWeight_nat_bracket_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:52:32.082102+00:00
-- url     : https://prove2.me/submissions/fb032be8-2d5f-44ae-80fe-6ce59e6043ae

-- Sol generated from Shared/UnimodalArgmaxBinomial.lean
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBinomial
import Definitions.Def_Shared_UnimodalArgmaxBracketing
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_ThresholdWindow_bracket_gap
import Theorems.Thm_Shared_UnimodalArgmaxBracketing_binomialWeight_thresholdWindow
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

/-- **The explicit comparison of the two bracketing degrees.**  For the binomial
weights the gap between the lower and the upper bracketing degree is `1` exactly
when the mode parameter `θ = (n+1)p/(p+q)` is an integer, and `0` otherwise. -/
theorem binomialWeight_bracket_gap (hp : 0 < p) (hq : 0 < q) :
    lastArgmax n (binomialWeight n p q) = firstArgmax n (binomialWeight n p q) + 1 ↔
      ∃ m : ℕ, (m : ℝ) = modeParameter n p q :=
  (binomialWeight_thresholdWindow hp hq).bracket_gap


/-! ## Dependence of the brackets on the parameters -/







/-! ## Arithmetic form of the comparison, and the classical case `p = q = 1` -/








/-! ## The largest term of the binomial expansion -/


/-! ## Every degree is a Newton-polygon vertex

Strict log-concavity says that the points `(k, log C(n,k))` are in *strictly convex
position*.  Equivalently: after tilting by a suitable weight `p^k` every single
degree `d ≤ n` becomes the **unique** maximiser.  This is the sweep of the argmax as
the threshold `θ` runs through `(0, n+1)`. -/



open Shared in
theorem solution{P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) :
    lastArgmax n (binomialWeight n (P : ℝ) (Q : ℝ))
        = firstArgmax n (binomialWeight n (P : ℝ) (Q : ℝ)) + 1 ↔
      (P + Q) ∣ (n + 1) * P := by
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hpq : (0 : ℝ) < (P : ℝ) + Q := by linarith
  rw [binomialWeight_bracket_gap hp hq]
  constructor
  · rintro ⟨m, hm⟩
    have : (m : ℝ) * ((P : ℝ) + Q) = ((n : ℝ) + 1) * P := by
      rw [hm, modeParameter, div_mul_cancel₀ _ hpq.ne']
    have hnat : m * (P + Q) = (n + 1) * P := by exact_mod_cast this
    exact ⟨m, by rw [← hnat]; ring⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hcr : ((n : ℝ) + 1) * P = c * ((P : ℝ) + Q) := by
      have : ((n + 1) * P : ℕ) = ((P + Q) * c : ℕ) := hc
      have := congrArg (Nat.cast : ℕ → ℝ) this
      push_cast at this
      linarith
    rw [modeParameter, hcr, mul_div_assoc, div_self hpq.ne', mul_one]
