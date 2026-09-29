-- Prove2me | Theorems.Thm_SingularModuli_total_work_ge
-- name    : SingularModuli.total_work_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:20:49.939051+00:00
-- url     : https://prove2.me/theorems/f191cd59-ffb1-4a1c-97b8-9eb0131f0959
-- title:
--   Raising the class number buys nothing.
-- statement:
--   **Raising the class number buys nothing.** Evaluating a degree-`h` polynomial
--   costs at least `h` ring operations (Horner), so the *total* expected arithmetic
--   work of the method is at least
--
--     `h · (N / S) ≥ h · √N/(4h) = √N/4`,
--
--   independently of `h`.  The apparent `1/h` speed-up in the number of evaluations
--   is exactly cancelled by the cost of one evaluation: there is no choice of
--   discriminant family that turns the method into a subexponential one.
--
--   ```lean
--   theorem SingularModuli.total_work_ge(hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
--       (hle : p ≤ q) (hbal : q ≤ 3 * p) (hH : H.Monic)
--       (hS : 0 < successCount H (p * q)) :
--       Real.sqrt ((p : ℝ) * q) / 4
--         ≤ (H.natDegree : ℝ) * (((p : ℝ) * q) / successCount H (p * q)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SingularModuli/Sharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SingularModuli/Sharpness.lean#L149

-- Thm stub generated from Cryptography/SingularModuli/Sharpness.lean
import Mathlib
import Definitions.Def_Cryptography_SingularModuli_RootCount
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier

/-!
# Singular Moduli Factoring, Step 6: the `√N` scaling is two-sided and sharp

`SqrtBarrier.lean` gives the *upper* bound `S ≤ h(p+q)` on the number of useful
evaluation points, i.e. a *lower* bound `√N/(4h)` on the expected number of
evaluations.  A lower bound alone would be compatible with the method never
working at all, so this file proves the complementary facts:

* `successCount_add_two_sq_eq` — **the bound `h(p+q)` is sharp**: when `H_D`
  splits completely modulo both primes (`r_p = r_q = h`, the generic
  CM-friendly case) the success count is exactly `h(p+q) - 2h²`;
* `successCount_eq_mul_of_no_root_right` — when `H_D` has roots mod `p` but none
  mod `q`, the success count is exactly `r_p · q`;
* `expected_trials_le` — in that case the expected number of evaluations is at
  most `p ≤ √N`: the method *does* work, in `Θ(√N)` time;
* `sqrt_scaling_two_sided` — combining the two: `√N/(4h) ≤ N/S ≤ √N`.  The
  singular moduli method is neither better nor worse than `√N` up to the factor
  `4h`;
* `successDensity_comp_le` — **reparametrisation does not help**: substituting
  any monic polynomial `g` for the evaluation variable multiplies the degree by
  `deg g`, so it degrades the bound by exactly the factor by which the
  evaluation cost grows.

The moral: the `√N` behaviour is not an artifact of a lower-bound technique; it
is the true order of the method.
-/

open SingularModuli

open Polynomial Finset FactoringBarriers

variable {p q : ℕ} {H : Polynomial ℤ}

/-! ## Sharpness of the counting bound -/






/-! ## The class number is not a free parameter -/

theorem SingularModuli.total_work_ge(hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hle : p ≤ q) (hbal : q ≤ 3 * p) (hH : H.Monic)
    (hS : 0 < successCount H (p * q)) :
    Real.sqrt ((p : ℝ) * q) / 4
      ≤ (H.natDegree : ℝ) * (((p : ℝ) * q) / successCount H (p * q)) := by sorry
