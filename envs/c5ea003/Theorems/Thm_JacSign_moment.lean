-- Prove2me | Theorems.Thm_JacSign_moment
-- name    : JacSign.moment
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:36:05.808387+00:00
-- url     : https://prove2.me/theorems/1087caa9-79b8-4454-b364-5c013d789e27
-- title:
--   The exact second moment over all quadratic twists.
-- statement:
--   **The exact second moment over all quadratic twists.**
--
--   ```lean
--   theorem JacSign.moment(hp : p ≠ 2) (h1 : p % 4 = 1) :
--       ∑ d : ZMod p, (A p d) ^ 2 = 2 * (p : ℤ) * ((p : ℤ) - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/JacobiSignedWeilFloorBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/JacobiSignedWeilFloorBound.lean#L171

-- Thm stub generated from Tropical/JacobiSignedWeilFloorBound.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore

/-!
# The Weil floor for the Jacobi-signed circle count

This file proves, completely elementarily (no algebraic geometry, no Hasse bound
imported), the **Weil bound**

`W p ^ 2 ≤ 4 * p`

for the Jacobi-signed circle count `W p = ∑_x χ(x(1-x²))` of
`JacobiSignedWeilFloorCore.lean`.  Equivalently `|W p| ≤ 2 √p`: the JACSIGN
statistic sits exactly at the square-root noise floor of a character sum.

The proof is a second-moment (averaging over quadratic twists) argument:

* `JacSign.chiSum_quadratic` : `∑_d χ((d-a)(d-b)) = p-1` if `a = b` and `-1` otherwise;
* `JacSign.A p d = ∑_x χ(x³ - d x)` is the trace of Frobenius of `y² = x³ - d x`;
* `JacSign.A_sq_scale` : `A p (c²) = χ(c) · A p 1` — all *square* twists carry the
  same squared trace;
* `JacSign.moment` : `∑_d (A p d)² = 2 p (p-1)` — the exact second moment;
* since squaring is at most `2`-to-`1`, the `p-1` scalings contribute
  `(p-1) · (A p 1)² ≤ 2 · 2p(p-1)`, whence `(A p 1)² ≤ 4p`.
-/

open Finset

open JacSign

variable (p : ℕ) [Fact p.Prime]

theorem JacSign.moment(hp : p ≠ 2) (h1 : p % 4 = 1) :
    ∑ d : ZMod p, (A p d) ^ 2 = 2 * (p : ℤ) * ((p : ℤ) - 1) := by sorry
