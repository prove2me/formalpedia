-- Prove2me | Theorems.Thm_JacSign_W_neg_reflect
-- name    : JacSign.W_neg_reflect
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:36:09.569025+00:00
-- url     : https://prove2.me/theorems/56b42b77-7864-4449-8db8-88c927b351ab
-- title:
--   Reflection identity: replacing `x` by `-x` multiplies the summand by `χ(-1)`.
-- statement:
--   Reflection identity: replacing `x` by `-x` multiplies the summand by `χ(-1)`.
--
--   ```lean
--   theorem JacSign.W_neg_reflect: W p = quadraticChar (ZMod p) (-1) * W p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/JacobiSignedWeilFloorCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/JacobiSignedWeilFloorCore.lean#L66

-- Thm stub generated from Tropical/JacobiSignedWeilFloorCore.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore

/-!
# The Jacobi-signed circle count: core structure (JACSIGN)

For an odd prime `p` let `χ = quadraticChar (ZMod p)` be the Legendre character and let

`S(p) = {(x, y) ∈ (ZMod p)² : x² + y² = 1}`

be the unit circle over `ZMod p`.  The *Jacobi-signed circle count* is the character
weighted point count

`circleWeight p = ∑_{(x,y) ∈ S(p)} χ(x)`.

This file proves the basic structure of this weight:

* `JacSign.circleWeight_eq_W` : the geometric weight collapses to the **cubic character sum**
  `W p = ∑_x χ(x(1 - x²))`, i.e. the trace of Frobenius of the curve `y² = x - x³`
  (up to sign).
* `JacSign.W_neg_reflect` : the reflection identity `W p = χ(-1) · W p`.
* `JacSign.W_eq_zero_of_three_mod_four` : `W p = 0` whenever `p ≡ 3 (mod 4)` — the
  supersingular half of the primes carries **no** signal at all.
* `JacSign.W_even` : `W p` is always even, so the weight can never be an odd number;
  this matches the observed data `-2, -10, 6, -18, 14, 22`.

These are the structural facts underlying the JACSIGN experiment; the Weil bound
`W p ^ 2 ≤ 4 p` is proved in `JacobiSignedWeilFloorBound.lean`.
-/

open Finset

open JacSign



variable (p : ℕ) [Fact p.Prime]

theorem JacSign.W_neg_reflect: W p = quadraticChar (ZMod p) (-1) * W p := by sorry
