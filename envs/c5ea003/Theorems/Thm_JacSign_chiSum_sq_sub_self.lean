-- Prove2me | Theorems.Thm_JacSign_chiSum_sq_sub_self
-- name    : JacSign.chiSum_sq_sub_self
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:35:48.488059+00:00
-- url     : https://prove2.me/theorems/a80c396b-41a4-4fb8-849e-2f89006e1cf1
-- title:
--   `∑_u χ(u² - u) = -1`: the basic nontrivial quadratic character sum.
-- statement:
--   `∑_u χ(u² - u) = -1`: the basic nontrivial quadratic character sum.
--
--   ```lean
--   theorem JacSign.chiSum_sq_sub_self(hp : p ≠ 2) :
--       ∑ u : ZMod p, quadraticChar (ZMod p) (u ^ 2 - u) = -1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/JacobiSignedWeilFloorBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/JacobiSignedWeilFloorBound.lean#L31

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

theorem JacSign.chiSum_sq_sub_self(hp : p ≠ 2) :
    ∑ u : ZMod p, quadraticChar (ZMod p) (u ^ 2 - u) = -1 := by sorry
