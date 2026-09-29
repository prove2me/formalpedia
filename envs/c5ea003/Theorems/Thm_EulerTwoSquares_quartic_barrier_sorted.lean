-- Prove2me | Theorems.Thm_EulerTwoSquares_quartic_barrier_sorted
-- name    : EulerTwoSquares.quartic_barrier_sorted
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:45:00.113797+00:00
-- url     : https://prove2.me/theorems/2afd44f5-73ea-4072-958f-4e499534926d
-- title:
--   The same statement symmetrised: the *larger* of the two small parts always exceeds
-- statement:
--   The same statement symmetrised: the *larger* of the two small parts always exceeds
--   `(2N)^{1/4}`.
--
--   ```lean
--   theorem EulerTwoSquares.quartic_barrier_sorted{N a b c d : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c)
--       (hcd : c ≤ d) (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N) (hne : ¬(a = c ∧ b = d)) :
--       2 * N < max a c ^ 4 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresBarrier.lean#L73

-- Thm stub generated from Algebra/EulerTwoSquaresBarrier.lean
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

theorem EulerTwoSquares.quartic_barrier_sorted{N a b c d : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c)
    (hcd : c ≤ d) (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N) (hne : ¬(a = c ∧ b = d)) :
    2 * N < max a c ^ 4 := by sorry
