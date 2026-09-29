-- Prove2me | Definitions.Def_NumberTheory_PrimeFractalBoxDimension
-- name    : NumberTheory_PrimeFractalBoxDimension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:21.00222+00:00
-- url     : https://prove2.me/theorems/fad41ee9-3ad5-457e-8ff9-11319f21654c
-- title:
--   Aether Catalog definitions — NumberTheory_PrimeFractalBoxDimension
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.PrimeFractalBoxDimension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/PrimeFractalBoxDimension.lean by skeleton subtraction
import Mathlib
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

namespace PrimeFractal

open Filter Topology

/-- Index of the box of size `1/m` containing the point `1 / log p`. -/
noncomputable def boxIndex (m p : ℕ) : ℕ := ⌊(m : ℝ) * logInv p⌋₊

/-- The set of boxes of size `1/m` that meet the prime fractal. -/
noncomputable def occupiedBoxes (m : ℕ) : Set ℕ := boxIndex m '' {p : ℕ | p.Prime}

/-- The box-counting function of the prime fractal at scale `1/m`. -/
noncomputable def boxCount (m : ℕ) : ℕ := (occupiedBoxes m).ncard

/-! ### Elementary bounds -/







/-! ### Separation of primes in the `d`-metric -/




/-! ### From Chebyshev to a lower bound on the box count -/



/-! ### Asymptotics -/







/-- The upper box-counting (Minkowski) dimension of the prime fractal. -/
noncomputable def upperBoxDim : ℝ := limsup (fun m : ℕ => Real.log (boxCount m) / Real.log m) atTop

/-- The lower box-counting (Minkowski) dimension of the prime fractal. -/
noncomputable def lowerBoxDim : ℝ := liminf (fun m : ℕ => Real.log (boxCount m) / Real.log m) atTop





end PrimeFractal


