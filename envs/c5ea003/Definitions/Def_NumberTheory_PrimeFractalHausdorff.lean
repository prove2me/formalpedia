-- Prove2me | Definitions.Def_NumberTheory_PrimeFractalHausdorff
-- name    : NumberTheory_PrimeFractalHausdorff
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:44.598325+00:00
-- url     : https://prove2.me/theorems/33972296-84d4-4baa-97d5-589c16090187
-- title:
--   Aether Catalog definitions — NumberTheory_PrimeFractalHausdorff
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.PrimeFractalHausdorff`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/PrimeFractalHausdorff.lean by skeleton subtraction
import Mathlib

/-!
# The "prime fractal": Hausdorff dimension and total length

We study the set of primes equipped with the metric

  `d p q = |1 / log p - 1 / log q|`,

as proposed in the research mission.  Concretely, the map
`logInv p = 1 / Real.log p` embeds the primes into `ℝ` and, by `Real.dist_eq`,
the metric induced from `ℝ` is exactly `d`.  We call the image the
*prime fractal* `primeFractal ⊆ ℝ`.

## Main results

* `logInv_injOn_prime` — `logInv` is injective on the primes, so
  `(primes, d)` is isometric to `primeFractal` with the euclidean metric.
* `dimH_primeFractal` — `dimH primeFractal = 0`.  **This refutes the mission
  conjecture `dimH = 1`, and a fortiori the conjecture `dimH = 1 + ε` with
  `ε > 0` measuring twin primes.**  The reason is soft but decisive: the primes
  are countable, and every countable subset of a metric space has Hausdorff
  dimension `0`.
* `dimH_subFractal` — the same holds for *every* subfamily of primes (twin
  primes, Sophie Germain primes, ...): the twin prime conjecture cannot change
  the Hausdorff dimension.
* `primeFractal_length_eq` / `tendsto_primeFractal_length` — the total
  `d`-length of the primes is *finite*, equal to `1 / log 2`.  The mission's
  heuristic ("the length is `∑ 1/(p log p) ∼ log log x`, which diverges") is
  therefore false twice over: the sum telescopes, and `∑ 1/(p log p)`
  converges anyway.
* `isCompact_insert_zero_primeFractal`, `dimH_closure_primeFractal` — the
  closure of the prime fractal is the compact set `{0} ∪ primeFractal`, and it
  still has Hausdorff dimension `0`.

The positive counterpart (the *box-counting* dimension really is `1`) is in
`NumberTheory.PrimeFractalBoxDimension`.
-/

namespace PrimeFractal

open Filter Topology

/-- The logarithmic embedding `p ↦ 1 / log p` of the primes into `ℝ`. -/
noncomputable def logInv (p : ℕ) : ℝ := 1 / Real.log p

/-- The prime fractal: the primes seen through the logarithmic lens. -/
noncomputable def primeFractal : Set ℝ := logInv '' {p : ℕ | p.Prime}










/-- The twin prime fractal. -/
noncomputable def twinPrimeFractal : Set ℝ := logInv '' {p : ℕ | p.Prime ∧ (p + 2).Prime}


/-!
### The total `d`-length of the primes is finite

The mission asserts that `∑_{p ≤ x} d(p, next p) ∼ log log x` diverges.  In fact
the sum telescopes and is bounded by `1 / log 2`.
-/



/-- The `n`-th prime, as a sequence. -/
noncomputable def primeSeq (n : ℕ) : ℕ := Nat.nth Nat.Prime n






/-!
### Topology: the closure of the prime fractal
-/






end PrimeFractal


