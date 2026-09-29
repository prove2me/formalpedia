-- Prove2me | Theorems.Thm_PrimeFractal_length_le
-- name    : PrimeFractal.length_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:32:27.608654+00:00
-- url     : https://prove2.me/theorems/03a37345-fdf6-462d-9d05-fc1127592228
-- title:
--   The `d`-length of any finite increasing chain of primes is at most `1 / log 2`:
-- statement:
--   The `d`-length of any finite increasing chain of primes is at most `1 / log 2`:
--   the prime fractal is a *rectifiable* set of finite length, not a divergent one.
--
--   ```lean
--   theorem PrimeFractal.length_le(q : ℕ → ℕ) (hq2 : ∀ i, 2 ≤ q i) (hmono : StrictMono q) (n : ℕ) :
--       ∑ i ∈ Finset.range n, dist (logInv (q i)) (logInv (q (i + 1))) ≤ 1 / Real.log 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/PrimeFractalHausdorff.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/PrimeFractalHausdorff.lean#L131

-- Thm stub generated from NumberTheory/PrimeFractalHausdorff.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalHausdorff

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

open PrimeFractal

open Filter Topology














/-!
### The total `d`-length of the primes is finite

The mission asserts that `∑_{p ≤ x} d(p, next p) ∼ log log x` diverges.  In fact
the sum telescopes and is bounded by `1 / log 2`.
-/

theorem PrimeFractal.length_le(q : ℕ → ℕ) (hq2 : ∀ i, 2 ≤ q i) (hmono : StrictMono q) (n : ℕ) :
    ∑ i ∈ Finset.range n, dist (logInv (q i)) (logInv (q (i + 1))) ≤ 1 / Real.log 2 := by sorry
