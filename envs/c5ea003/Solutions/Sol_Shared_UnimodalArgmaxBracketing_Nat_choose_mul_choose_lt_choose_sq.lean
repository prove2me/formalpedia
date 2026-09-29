-- Prove2me | solution 1 for Shared.UnimodalArgmaxBracketing.Nat.choose_mul_choose_lt_choose_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:41:38.789411+00:00
-- url     : https://prove2.me/submissions/c324559d-aa2f-4876-a985-5b7eae30a233

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
theorem solution{n k : ℕ} (h : k + 2 ≤ n) :
    n.choose k * n.choose (k + 2) < (n.choose (k + 1)) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + 2 + m := ⟨n - k - 2, by omega⟩
  set N := k + 2 + m with hN
  have e1 : N - k = m + 2 := by omega
  have e2 : N - (k + 1) = m + 1 := by omega
  have k1 : N.choose (k + 1) * (k + 1) = N.choose k * (m + 2) := by
    rw [Nat.choose_succ_right_eq, e1]
  have k2 : N.choose (k + 2) * (k + 2) = N.choose (k + 1) * (m + 1) := by
    rw [show k + 2 = (k + 1) + 1 from rfl, Nat.choose_succ_right_eq, e2]
  have hA : 0 < N.choose k := Nat.choose_pos (by omega)
  have hB : 0 < N.choose (k + 1) := Nat.choose_pos (by omega)
  have hC : 0 < N.choose (k + 2) := Nat.choose_pos (by omega)
  -- the crucial identity `B² (k+1)(m+1) = A C (m+2)(k+2)`
  have key : (N.choose (k + 1)) ^ 2 * ((k + 1) * (m + 1))
      = N.choose k * N.choose (k + 2) * ((m + 2) * (k + 2)) :=
    calc (N.choose (k + 1)) ^ 2 * ((k + 1) * (m + 1))
        = (N.choose (k + 1) * (k + 1)) * (N.choose (k + 1) * (m + 1)) := by ring
      _ = (N.choose k * (m + 2)) * (N.choose (k + 2) * (k + 2)) := by rw [k1, ← k2]
      _ = N.choose k * N.choose (k + 2) * ((m + 2) * (k + 2)) := by ring
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < N.choose k * N.choose (k + 2) := Nat.mul_pos hA hC
  nlinarith [key, hcon, hpos]
