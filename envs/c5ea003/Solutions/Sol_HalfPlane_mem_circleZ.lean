-- Prove2me | solution 1 for HalfPlane.mem_circleZ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:49:51.830195+00:00
-- url     : https://prove2.me/submissions/acd9122e-853d-4e83-87d1-65ee568e9367

-- Sol generated from MachineLearning/HalfPlaneCircleBasic.lean
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






/-! ### Small-case data (Lab Notes)

```
N :  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20
C :  1  2  4  8  4  8  8 16 12  8 12 32 12 16 16 32 16 24 20 32
H :  1  0  2  2  2  2  2  4  4  2  2  6  2  2  4  6  3  4  4  6
```
-/

example : circleCount 15 = 16 := by decide
example : circleCount 3 * circleCount 5 = 16 := by decide
example : halfPlaneCount 35 = 6 := by decide
example : halfPlaneCount 5 * halfPlaneCount 7 = 4 := by decide


open HalfPlane in
theorem solution{N : ℕ} [NeZero N] {q : ZMod N × ZMod N} :
    q ∈ circleZ N ↔ q.1 ^ 2 + q.2 ^ 2 = 1 := by
  simp [circleZ]
