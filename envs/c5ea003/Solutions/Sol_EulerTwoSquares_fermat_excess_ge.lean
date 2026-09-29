-- Prove2me | solution 1 for EulerTwoSquares.fermat_excess_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T18:57:10.225355+00:00
-- url     : https://prove2.me/submissions/6c201258-88a6-4c77-8fa5-f743de85b6f1

-- Sol generated from Algebra/EulerTwoSquaresCost.lean
import Mathlib

/-!
# The cost face: Fermat's scan is short exactly when the factors are balanced

Euler's factorisation method must first *find* two representations `N = a²+b² = c²+d²`; the
competing classical method (Fermat's difference-of-squares scan) walks `s = ⌈√N⌉, ⌈√N⌉+1, …`
until `s² - N` is a square.  This file proves the exact arithmetic of the Fermat scan, which
is what makes the empirical comparison ("Euler needs two representation searches and loses by
a constant factor, catastrophically so on balanced factorisations") a statement about a
quantity one can compute.

* `EulerTwoSquares.fermat_identity` — correctness: with `p + q = 2u` and `q = p + 2v` one has
  `u² = p*q + v²`, i.e. the scan does terminate, at `s = u = (p+q)/2`.
* `EulerTwoSquares.sqrt_eq_iff_of_add_sq` — the exact criterion for `⌊√N⌋`:
  if `N + t² = (w+1)²` and `t > 0` then `⌊√N⌋ = w ↔ t² < 2(w+1)`.
* `EulerTwoSquares.fermat_halts_immediately_iff` — consequence: Fermat's scan succeeds on its
  **first** trial iff `(q-p)² < 4(p+q)`, i.e. exactly on the balanced instances.
* `EulerTwoSquares.fermat_excess_le` — the real-analytic bound
  `(p+q)/2 - √(pq) ≤ (q-p)²/(8√(pq))`, so the whole scan has length
  `O((q-p)²/√N)`: quadratically small in the imbalance.
* `EulerTwoSquares.fermat_excess_ge` — the matching lower bound
  `(q-p)²/(8·max p q) ≤ (p+q)/2 - √(pq)`, so the estimate is sharp up to a constant.
-/


/-! ## Correctness of the difference-of-squares step -/


/-! ## The exact position of the start of the scan -/



/-! ## The length of the scan, analytically -/




theorem solution{p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (q - p) ^ 2 / (8 * max p q) ≤ (p + q) / 2 - Real.sqrt (p * q) := by
  set x := Real.sqrt p with hxdef
  set y := Real.sqrt q with hydef
  have hx : 0 < x := Real.sqrt_pos.2 hp
  have hy : 0 < y := Real.sqrt_pos.2 hq
  have hx2 : x ^ 2 = p := Real.sq_sqrt hp.le
  have hy2 : y ^ 2 = q := Real.sq_sqrt hq.le
  have hs : Real.sqrt (p * q) = x * y := by rw [hxdef, hydef, ← Real.sqrt_mul hp.le]
  have hm : (0 : ℝ) < max p q := lt_max_of_lt_left hp
  rw [hs, div_le_iff₀ (by positivity)]
  have hmx : x ^ 2 ≤ max p q := by rw [hx2]; exact le_max_left _ _
  have hmy : y ^ 2 ≤ max p q := by rw [hy2]; exact le_max_right _ _
  have hxy : (x + y) ^ 2 ≤ 4 * max p q := by nlinarith [sq_nonneg (x - y)]
  have hkey : (q - p) ^ 2 = (y - x) ^ 2 * (x + y) ^ 2 := by
    rw [← hx2, ← hy2]; ring
  rw [hkey]
  nlinarith [sq_nonneg (x - y), mul_pos hx hy, sq_nonneg (x + y)]
