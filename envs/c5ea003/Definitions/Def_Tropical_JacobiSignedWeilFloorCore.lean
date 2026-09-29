-- Prove2me | Definitions.Def_Tropical_JacobiSignedWeilFloorCore
-- name    : Tropical_JacobiSignedWeilFloorCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:30:18.774017+00:00
-- url     : https://prove2.me/theorems/ad575a2a-656f-4adc-b793-16ee88f05f2f
-- title:
--   Aether Catalog definitions — Tropical_JacobiSignedWeilFloorCore
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.JacobiSignedWeilFloorCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/JacobiSignedWeilFloorCore.lean by skeleton subtraction
import Mathlib

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

namespace JacSign

/-- The character sum `W p = ∑_x χ(x (1 - x²))`, where `χ` is the Legendre character. -/
noncomputable def W (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ x : ZMod p, quadraticChar (ZMod p) (x * (1 - x ^ 2))

/-- The Jacobi-signed circle count: the points of the unit circle `x² + y² = 1` over
`ZMod p`, each weighted by the Legendre symbol of its `x`-coordinate. -/
noncomputable def circleWeight (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ x : ZMod p, ∑ y : ZMod p, if x ^ 2 + y ^ 2 = 1 then quadraticChar (ZMod p) x else 0

variable (p : ℕ) [Fact p.Prime]






/-- The "lower half" of the nonzero residues: one representative of each pair
`{x, -x}`. -/
def halfSet (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (univ.filter (fun x : ZMod p => 2 * x.val < p)).erase 0




end JacSign


