-- Prove2me | Theorems.Thm_EulerTwoSquares_fermat_halts_immediately_iff
-- name    : EulerTwoSquares.fermat_halts_immediately_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:45:34.28321+00:00
-- url     : https://prove2.me/theorems/f11885a1-55a4-44d2-8fbb-208e7258a821
-- title:
--   Fermat's scan halts on its first trial exactly on balanced instances.
-- statement:
--   **Fermat's scan halts on its first trial exactly on balanced instances.**  For
--   `N = p*q` with `p + q = 2u`, `q = p + 2v` and `v > 0`, the first trial value `⌊√N⌋ + 1`
--   already equals the target `u = (p+q)/2` iff `v² < 2u`, i.e. iff `(q-p)² < 4(p+q)`.
--
--   ```lean
--   theorem EulerTwoSquares.fermat_halts_immediately_iff{p q u v : ℕ} (hu : p + q = 2 * u) (hv : q = p + 2 * v)
--       (hv0 : 0 < v) :
--       Nat.sqrt (p * q) + 1 = u ↔ v ^ 2 < 2 * u := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresCost.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresCost.lean#L53

-- Thm stub generated from Algebra/EulerTwoSquaresCost.lean
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

theorem EulerTwoSquares.fermat_halts_immediately_iff{p q u v : ℕ} (hu : p + q = 2 * u) (hv : q = p + 2 * v)
    (hv0 : 0 < v) :
    Nat.sqrt (p * q) + 1 = u ↔ v ^ 2 < 2 * u := by sorry
