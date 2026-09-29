-- Prove2me | Theorems.Thm_HalfPlane_mem_circleZ
-- name    : HalfPlane.mem_circleZ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:33:47.293559+00:00
-- url     : https://prove2.me/theorems/6cd6d62a-01c5-4e14-a9ad-6f85df185f4a
-- title:
--   Mem circleZ
-- statement:
--   Formal statement of `HalfPlane.mem_circleZ` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem HalfPlane.mem_circleZ{N : ℕ} [NeZero N] {q : ZMod N × ZMod N} :
--       q ∈ circleZ N ↔ q.1 ^ 2 + q.2 ^ 2 = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneCircleBasic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneCircleBasic.lean#L61

-- Thm stub generated from MachineLearning/HalfPlaneCircleBasic.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic

/-!
# The half-plane circle count: basic definitions

For a modulus `N` we study the *modular circle*

  `Circle(N) = {(x, y) ∈ [0,N)² : x² + y² ≡ 1 (mod N)}`

together with the **non-CRT-separable** half-plane cut `x + y < N/2`
(the sum `x + y` is taken as an *integer*, not modulo `N`, which is exactly
what destroys separability).

This file sets up:

* `circleFinset N`  — the circle as a finite set of pairs of naturals,
* `circleCount N`   — its cardinality `C(N)`,
* `halfPlaneCount N`— the count `H(N)` of circle points in the low half-plane
  `2(x+y) < N`,
* `highCount N`     — the count of circle points with `2(x+y) > 3N`,
* `unitRootCount N` — the number of square roots of `1` below `N/2`,

and the bridge to the algebraic description of the circle inside `ZMod N`,
which is what makes the Chinese Remainder analysis possible.
-/

open HalfPlane

open Finset








variable {N : ℕ}

theorem HalfPlane.mem_circleZ{N : ℕ} [NeZero N] {q : ZMod N × ZMod N} :
    q ∈ circleZ N ↔ q.1 ^ 2 + q.2 ^ 2 = 1 := by sorry
