-- Prove2me | Definitions.Def_Tropical_JacobiSignedWeilFloorBound
-- name    : Tropical_JacobiSignedWeilFloorBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:31:01.704826+00:00
-- url     : https://prove2.me/theorems/f3776855-1cf8-49cb-ac8c-d8c6f53b0758
-- title:
--   Aether Catalog definitions — Tropical_JacobiSignedWeilFloorBound
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.JacobiSignedWeilFloorBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/JacobiSignedWeilFloorBound.lean by skeleton subtraction
import Mathlib
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

namespace JacSign

variable (p : ℕ) [Fact p.Prime]



/-- `A p d` is the character sum of the quadratic twist `y² = x³ - d x`
(the negative of its trace of Frobenius). -/
noncomputable def A (p : ℕ) [Fact p.Prime] (d : ZMod p) : ℤ :=
  ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - d * x)










end JacSign


