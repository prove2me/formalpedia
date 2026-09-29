-- Prove2me | Theorems.Thm_PrimeFractal_twin_dist_le
-- name    : PrimeFractal.twin_dist_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:34:24.229638+00:00
-- url     : https://prove2.me/theorems/f1246461-e266-4596-b53f-fbda0aa69ea3
-- title:
--   Corrected twin scale.
-- statement:
--   **Corrected twin scale.** A twin pair is at `d`-distance at most `2 / (p (log p)^2)`.
--
--   ```lean
--   theorem PrimeFractal.twin_dist_le{p : ℕ} (hp : 2 ≤ p) :
--       dist (logInv p) (logInv (p + 2)) ≤ 2 / ((p : ℝ) * (Real.log p) ^ 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/PrimeFractalTwin.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/PrimeFractalTwin.lean#L28

-- Thm stub generated from NumberTheory/PrimeFractalTwin.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalHausdorff

/-!
# No fractal dust: the metric structure of twin primes in the prime fractal

The mission's conjecture rests on the picture that "twin primes create a fractal
dust that increases the dimension".  Here we show that the picture is wrong in
a precise, structural way.

* `twin_dist_le` — a twin pair `(p, p+2)` sits at `d`-distance at most
  `2 / (p (log p)^2)`, *not* `∼ 1 / (p log p)` as the mission asserts: the
  mission's heuristic overestimates the twin scale by a factor `log p`.
* `finite_of_le_logInv` — only finitely many primes lie above any positive
  height, so
* `primeFractal_isolated` — **every point of the prime fractal is isolated**.
  A countable, uniformly discrete-away-from-`0` set carries no dust at any
  scale: the accumulation happens only at the single point `0`.
* `zero_mem_closure_iff_infinite` — for any family `T` of primes, `0` is in the
  closure of the corresponding subfractal iff `T` is infinite.  Applied to the
  twin primes (`twin_conjecture_iff_zero_mem_closure`) this turns the twin
  prime conjecture into a purely metric statement about a single point of `ℝ`
  — and that point contributes nothing to any dimension.
-/

open PrimeFractal

open Filter Topology

theorem PrimeFractal.twin_dist_le{p : ℕ} (hp : 2 ≤ p) :
    dist (logInv p) (logInv (p + 2)) ≤ 2 / ((p : ℝ) * (Real.log p) ^ 2) := by sorry
