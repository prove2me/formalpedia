-- Prove2me | Theorems.Thm_PrimeFractal_tendsto_intBoxCount_log_div
-- name    : PrimeFractal.tendsto_intBoxCount_log_div
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:34:14.576352+00:00
-- url     : https://prove2.me/theorems/6e27be5c-8c1e-43b0-8347-ac3394df3ba3
-- title:
--   The integer fractal also has box dimension `1`.
-- statement:
--   **The integer fractal also has box dimension `1`.**
--
--   ```lean
--   theorem PrimeFractal.tendsto_intBoxCount_log_div:
--       Tendsto (fun m : ℕ => Real.log (intBoxCount m) / Real.log m) atTop (𝓝 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/PrimeFractalIntegers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/PrimeFractalIntegers.lean#L131

-- Thm stub generated from NumberTheory/PrimeFractalIntegers.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalIntegers

/-!
# The logarithmic lens cannot see primality

The same construction applied to *all* integers `≥ 2` produces the "integer
fractal" `{1 / log n : n ≥ 2}`.  We show it has

* Hausdorff dimension `0` (it is countable), and
* box-counting dimension `1` (`tendsto_intBoxCount_log_div`),

exactly like the prime fractal.  The proof of the lower bound is the same
separation estimate `boxIndex_lt`, but with no arithmetic input at all: for
integers one may simply count `Y - 1` of them below `Y`, where the primes needed
Chebyshev's theorem.

**Conclusion.** Both dimensions agree for the primes and for all integers, so
neither can detect primality: the mission's programme of reading off arithmetic
information (twin primes) from `dim (P, d)` is structurally impossible.  The
difference between the two sets is only visible in the second-order term (the
number of occupied boxes; see `NumberTheory.PrimeFractalRefined`).
-/

open PrimeFractal

open Filter Topology

theorem PrimeFractal.tendsto_intBoxCount_log_div:
    Tendsto (fun m : ℕ => Real.log (intBoxCount m) / Real.log m) atTop (𝓝 1) := by sorry
