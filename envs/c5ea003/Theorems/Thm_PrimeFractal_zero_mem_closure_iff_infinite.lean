-- Prove2me | Theorems.Thm_PrimeFractal_zero_mem_closure_iff_infinite
-- name    : PrimeFractal.zero_mem_closure_iff_infinite
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:34:35.892734+00:00
-- url     : https://prove2.me/theorems/2869f38a-8ffb-4a0f-844b-c49b441d6622
-- title:
--   For any family `T` of primes, `0` lies in the closure of the corresponding
-- statement:
--   For any family `T` of primes, `0` lies in the closure of the corresponding
--   subfractal exactly when `T` is infinite.
--
--   ```lean
--   theorem PrimeFractal.zero_mem_closure_iff_infinite{T : Set ℕ} (hT : ∀ p ∈ T, Nat.Prime p) :
--       (0 : ℝ) ∈ closure (logInv '' T) ↔ T.Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/PrimeFractalTwin.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/PrimeFractalTwin.lean#L116

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

theorem PrimeFractal.zero_mem_closure_iff_infinite{T : Set ℕ} (hT : ∀ p ∈ T, Nat.Prime p) :
    (0 : ℝ) ∈ closure (logInv '' T) ↔ T.Infinite := by sorry
