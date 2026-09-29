-- Prove2me | Theorems.Thm_JacSign_jacobsthal_identity
-- name    : JacSign.jacobsthal_identity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:03.189857+00:00
-- url     : https://prove2.me/theorems/9a01e46c-8cf4-422e-9987-fa02ddaa4820
-- title:
--   The Jacobsthal identity.
-- statement:
--   **The Jacobsthal identity.** For `p ≡ 1 (mod 4)` and any quadratic nonresidue `ν`,
--   the residue twist and the nonresidue twist of `y² = x³ - x` satisfy
--   `A(1)² + A(ν)² = 4p`.
--
--   ```lean
--   theorem JacSign.jacobsthal_identity(hp : p ≠ 2) (h1 : p % 4 = 1) {v : ZMod p}
--       (hv : quadraticChar (ZMod p) v = -1) : (A p 1) ^ 2 + (A p v) ^ 2 = 4 * (p : ℤ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/JacobiSignedTwoSquares.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/JacobiSignedTwoSquares.lean#L68

-- Thm stub generated from Tropical/JacobiSignedTwoSquares.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound

/-!
# The Weil floor is a two-squares identity

The Weil bound `W p ^ 2 ≤ 4 p` of `JacobiSignedWeilFloorBound.lean` is not an accident of
estimation: it is the shadow of an **exact identity**.  Write `A p d = ∑_x χ(x³ - d x)` for
the twisted character sums, and let `ν` be any quadratic nonresidue mod `p`.  For
`p ≡ 1 (mod 4)` we prove

`A p 1 ^ 2 + A p ν ^ 2 = 4 p`   (`JacSign.jacobsthal_identity`)

so the Jacobi-signed circle count `W p = A p 1` and its nonresidue twin `A p ν` are the two
legs of a right triangle with hypotenuse `2 √p`.  Consequences:

* `JacSign.W_sq_add_twist_sq` : the identity phrased for the statistic `W p` itself;
* `JacSign.weil_floor_of_identity` : the Weil bound, re-derived as a corollary;
* `JacSign.two_squares_of_one_mod_four` : **Fermat's two-square theorem** with explicit
  witnesses `p = (W p / 2)² + (A p ν / 2)²` — the signal and its twin are *exactly* the
  Gaussian-integer coordinates of `p`.

Structurally this explains the experimental data: `W p` is `2a` where `p = a² + b²`, hence
its erratic, "unstructured" behaviour, and hence also its inability to leak the factors of
a semiprime — the two legs trade off against each other with `4p` conserved.
-/

open Finset

open JacSign

variable (p : ℕ) [Fact p.Prime]

theorem JacSign.jacobsthal_identity(hp : p ≠ 2) (h1 : p % 4 = 1) {v : ZMod p}
    (hv : quadraticChar (ZMod p) v = -1) : (A p 1) ^ 2 + (A p v) ^ 2 = 4 * (p : ℤ) := by sorry
