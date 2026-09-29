-- Prove2me | Theorems.Thm_PrimeFractal_logInv_pos
-- name    : PrimeFractal.logInv_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:32:37.120881+00:00
-- url     : https://prove2.me/theorems/49b244ef-e1ae-45e8-8072-cbaaac73819f
-- title:
--   LogInv pos
-- statement:
--   Formal statement of `PrimeFractal.logInv_pos` from the Aether Catalog (NumberTheory). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PrimeFractal.logInv_pos{p : ℕ} (hp : p.Prime) : 0 < logInv p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/PrimeFractalHausdorff.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/PrimeFractalHausdorff.lean#L55

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

theorem PrimeFractal.logInv_pos{p : ℕ} (hp : p.Prime) : 0 < logInv p := by sorry
