-- Prove2me | solution 1 for EulerTwoSquares.quartic_barrier_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T18:53:46.52626+00:00
-- url     : https://prove2.me/submissions/7f86378e-bf9b-4276-a118-13deb37cc6b6

-- Sol generated from Algebra/EulerTwoSquaresBarrier.lean
import Mathlib

/-!
# An unconditional quartic barrier for representation search

Euler's method has to *find* two essentially distinct representations `N = a²+b² = c²+d²`.
The natural search walks the smaller part upward, `1, 2, 3, …`, testing whether `N - a²` is a
square.  How far must such a walk go before it has seen **both** representations?

This file answers that with an exact, unconditional inequality.  Write the two
representations in sorted form `a ≤ b`, `c ≤ d`.  If they are different then their large
parts differ, say `d < b`, hence `b ≥ d + 1` and therefore

`c² = b² - d² + a² ≥ 2d + 1`,   while   `2N = 2c² + 2d² ≤ 4d² < (2d+1)²`,

so `2N < c⁴`.  In other words **the larger of the two small parts exceeds `(2N)^{1/4}`**
(`EulerTwoSquares.quartic_barrier`, `EulerTwoSquares.euler_scan_quartic_bound`).  No primality,
no genericity, no averaging: two distinct representations simply cannot both be "shallow".

Combined with `EulerTwoSquares.fermat_halts_immediately_iff` this gives the sharpest form of
the cost comparison (`EulerTwoSquares.euler_loses_on_balanced`): on a balanced eligible
semiprime — where Fermat's difference-of-squares scan succeeds on its *first* trial — any
representation search that collects both representations must reach a bound `t` with
`t⁴ > 2N`, i.e. `t > (2N)^{1/4}`.  The measured constant-factor loss of the representation
route is therefore not an artefact of the sampling distribution on the balanced side: it is
forced.
-/


/-! ## The barrier -/






/-! ## EULER-LOSES on balanced instances -/

variable {p q : ℕ}




theorem solution{N a b c d k : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c)
    (hcd : c ≤ d) (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N) (hk : 0 < k)
    (hgap : d + k ≤ b) : 2 * k ^ 2 * N < c ^ 4 := by
  have hd0 : 0 ≤ d := le_trans hc hcd
  have hc2 : 2 * k * d + k ^ 2 ≤ c ^ 2 := by nlinarith
  have h2kd : 0 ≤ 2 * k * d := by nlinarith
  have hk2 : 0 < k ^ 2 := by positivity
  have hXpos : 0 < 2 * k * d + k ^ 2 := by linarith
  have hsq : (2 * k * d + k ^ 2) ^ 2 ≤ (c ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc2) (by linarith : (0 : ℤ) ≤ c ^ 2 + (2 * k * d + k ^ 2))]
  have hexp : (2 * k * d + k ^ 2) ^ 2 = 4 * k ^ 2 * d ^ 2 + 4 * k ^ 3 * d + k ^ 4 := by ring
  have hc4 : c ^ 4 = (c ^ 2) ^ 2 := by ring
  have hNd : N ≤ 2 * d ^ 2 := by nlinarith
  have hNk : 2 * k ^ 2 * N ≤ 4 * k ^ 2 * d ^ 2 := by
    nlinarith [mul_nonneg hk2.le (sub_nonneg.2 hNd)]
  have hk4 : 0 < k ^ 4 := by positivity
  have hk3d : 0 ≤ 4 * k ^ 3 * d := by positivity
  linarith
