-- Prove2me | Definitions.Def_NumberTheory_PrimeFractalIntegers
-- name    : NumberTheory_PrimeFractalIntegers
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:30.770971+00:00
-- url     : https://prove2.me/theorems/91a84f1a-ed64-4789-b055-8f1f8d1d45c1
-- title:
--   Aether Catalog definitions — NumberTheory_PrimeFractalIntegers
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.PrimeFractalIntegers`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/PrimeFractalIntegers.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalHausdorff

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

namespace PrimeFractal

open Filter Topology

/-- The integer fractal: all integers `≥ 2` through the logarithmic lens. -/
noncomputable def intFractal : Set ℝ := logInv '' {n : ℕ | 2 ≤ n}

/-- Boxes of size `1/m` occupied by the integer fractal. -/
noncomputable def intBoxCount (m : ℕ) : ℕ := (boxIndex m '' {n : ℕ | 2 ≤ n}).ncard










end PrimeFractal


