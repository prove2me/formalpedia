-- Prove2me | Theorems.Thm_ECMParity_two_dvd_curveCard_iff
-- name    : ECMParity.two_dvd_curveCard_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:30:17.391068+00:00
-- url     : https://prove2.me/theorems/21f14d8e-cf92-4f0f-ba20-1afb93d9338b
-- title:
--   Parity dichotomy.
-- statement:
--   **Parity dichotomy.**  For a separable cubic, the projective point count of
--   `y² = x³ + A x + B` over `𝔽_p` (`p` odd) is even iff the cubic has a root.
--
--   ```lean
--   theorem ECMParity.two_dvd_curveCard_iff(hp : p ≠ 2) (A B : ZMod p) (hd : disc A B ≠ 0) :
--       2 ∣ curveCard A B ↔ ∃ x : ZMod p, cubic A B x = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ECMParityCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ECMParityCore.lean#L242

-- Thm stub generated from Algebra/ECMParityCore.lean
import Mathlib
import Definitions.Def_Algebra_ECMParityCore
/-
# ECM-PARITY, core: the parity of the point count of `y² = x³ + A x + B`

For an odd prime `p` and `A B : ZMod p` put

  `curveCard A B = 1 + #{(x,y) ∈ (ZMod p)² : y² = x³ + A x + B}`

(the `1` is the point at infinity of the projective Weierstrass model).

The main result of this file is the **parity dichotomy**

  `2 ∣ curveCard A B  ↔  the cubic x³ + A x + B has a root in ZMod p`

valid whenever the cubic is separable (`Δ = -4A³ - 27B² ≠ 0`).  Equivalently:
`#E` is odd exactly when Frobenius is a `3`-cycle on the roots of the cubic
(the cubic is irreducible over `𝔽_p`; see `ECMParityFrobenius.lean`).

The proof is elementary and self-contained:

* fibrewise counting: over each `x` the fibre `{y : y² = f x}` has odd
  cardinality iff `f x = 0`, hence `#affine ≡ #roots (mod 2)`;
* a separable cubic has `0`, `1` or `3` roots (never `2`), so `#roots` is odd
  iff `#roots ≠ 0`.

§0 collects the purely algebraic facts about a depressed cubic over an arbitrary
field (Vieta, the third root, the discriminant as a square of the root
difference product).  These are reused over the cubic extension `𝔽_{p³}` in
`ECMParityFrobenius.lean`.
-/

open ECMParity

open Finset

/-! ## 0. Depressed cubics over an arbitrary field -/




variable {F : Type*} [Field F] {A B a b x : F}









/-! ## 1. Fibrewise counting over `𝔽_p` -/

variable {p : ℕ} [Fact p.Prime]








/-! ## 2. A separable cubic has `0`, `1` or `3` roots -/




/-! ## 3. The parity dichotomy -/

theorem ECMParity.two_dvd_curveCard_iff(hp : p ≠ 2) (A B : ZMod p) (hd : disc A B ≠ 0) :
    2 ∣ curveCard A B ↔ ∃ x : ZMod p, cubic A B x = 0 := by sorry
