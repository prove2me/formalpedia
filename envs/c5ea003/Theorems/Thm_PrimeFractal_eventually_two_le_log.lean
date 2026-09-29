-- Prove2me | Theorems.Thm_PrimeFractal_eventually_two_le_log
-- name    : PrimeFractal.eventually_two_le_log
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:31:00.510606+00:00
-- url     : https://prove2.me/theorems/b02470b8-abe0-40ee-ade3-04d48d08eba0
-- title:
--   Eventually two le log
-- statement:
--   Formal statement of `PrimeFractal.eventually_two_le_log` from the Aether Catalog (NumberTheory). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PrimeFractal.eventually_two_le_log: ∀ᶠ m : ℕ in atTop, (2 : ℝ) ≤ Real.log m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/PrimeFractalBoxDimension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/PrimeFractalBoxDimension.lean#L223

-- Thm stub generated from NumberTheory/PrimeFractalBoxDimension.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalHausdorff

/-!
# The box-counting dimension of the prime fractal is exactly `1`

`NumberTheory.PrimeFractalHausdorff` shows that the Hausdorff dimension of the
prime fractal `{1 / log p : p prime} ⊆ ℝ` is `0`, refuting the mission
conjecture.  Here we prove the *positive* half of the story: the notion that
actually sees the conjectured value is the **box-counting (Minkowski)
dimension**, and for the prime fractal it equals `1` on the nose.

At scale `1/m` we count the boxes `[k/m, (k+1)/m)` that meet the prime fractal,
i.e. the cardinality `boxCount m` of the set of values `⌊m / log p⌋` over primes
`p`.  The two halves are:

* `boxCount_le` : `boxCount m ≤ 2m + 1` — a trivial upper bound valid for any
  subset of an interval, which is what forces the dimension to be `≤ 1`.  In
  particular *no* configuration of primes — twin primes included — can produce
  a dimension `1 + ε` with `ε > 0`.
* `eventually_boxCount_ge` : `boxCount m ≥ m / (16 (log m)^4)`.  This is the
  arithmetic input: it uses the Chebyshev-type lower bound
  `PrimeFractal.le_primeCounting_mul_log` together with the observation that
  `p ↦ ⌊m / log p⌋` is injective on primes `p ≤ Y` as soon as
  `2 Y (log Y)^2 ≤ m` (primes below `Y` are spread more than `1/m` apart in the
  `d`-metric).

Together they give `tendsto_boxCount_log_div`: `log (boxCount m) / log m → 1`,
hence `upperBoxDim = lowerBoxDim = 1` (`upperBoxDim_eq_one`,
`lowerBoxDim_eq_one`), while the Hausdorff dimension is `0`
(`dimH_lt_boxDim`).  The prime fractal is therefore a *dimension-irregular*
set: box and Hausdorff dimensions disagree maximally.
-/

open PrimeFractal

open Filter Topology




/-! ### Elementary bounds -/







/-! ### Separation of primes in the `d`-metric -/




/-! ### From Chebyshev to a lower bound on the box count -/



/-! ### Asymptotics -/

theorem PrimeFractal.eventually_two_le_log: ∀ᶠ m : ℕ in atTop, (2 : ℝ) ≤ Real.log m := by sorry
