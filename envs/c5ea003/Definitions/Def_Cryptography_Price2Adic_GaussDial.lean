-- Prove2me | Definitions.Def_Cryptography_Price2Adic_GaussDial
-- name    : Cryptography_Price2Adic_GaussDial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:22:39.82089+00:00
-- url     : https://prove2.me/theorems/2973a3a0-0684-4c7d-88a8-fd1a215f58d7
-- title:
--   Aether Catalog definitions — Cryptography_Price2Adic_GaussDial
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.Price2Adic.GaussDial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/Price2Adic/GaussDial.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Core

/-!
# Gauss-sum magnitudes are an information-free residue dial

The experiment behind this file compared numeric quadratic Gauss sums with their closed
forms on `7625` parameter cells `(a, b, M)` and found that every `|G|`-magnitude feature
is a pure function of a residue class — on the standard lab range, literally constant.
Here that observation is proved, in the model of `Cryptography.ResidueDial.Core`.

Fix an odd prime `p`, let `χ` be the quadratic character of `ZMod p` (valued in `ℂ`) and
let `ψ` be a primitive additive character.  Then:

* `gaussSum_sq_eq` — `g² = ± p`, with the sign `+` exactly when `p ≡ 1 (mod 4)`.  The
  *sign* feature is therefore a dial of modulus `4` (`gaussSum_sq_residue_dial`).
* `norm_gaussSum` — `‖g‖ = √p`: the magnitude does not depend on `ψ` at all.
* `norm_gaussSum_mulShift` — twisting `ψ` by any unit `a ∈ (ZMod p)ˣ` leaves `‖g‖`
  unchanged.  So the magnitude, read as a function of the residue class `a`, is
  **constant**: it separates no class from any other.
* `ResidueDial.speedup_of_constant_feature` — a constant feature always induces a dial of
  density `0` or `1`, hence a speedup of exactly `1`: zero bits.
* `gaussMagnitude_dial_speedup_eq_one` — combining the two: the Gauss-magnitude dial buys
  a scan speedup of exactly `1`.  This is the "`I = 0` bits" claim, proved rather than
  measured, and it sits strictly below the universal cap `4/3` of
  `ResidueDial.dialSpeedup_le_four_thirds`.

## Lab notes (round 70, exp 548)

All `7625` cells matched the closed form (`|G| ∈ {0, √M, √(2M)}`), and on the lab range
(`p ≡ q mod 4`) the normalised magnitude was constant to machine precision, giving an
empirical mutual information of `0` bits with a residue entropy of `H = 1.000`.  The
theorems below explain why no sampling could have found anything else.
-/

open Finset

namespace ResidueDial


end ResidueDial

namespace Price2Adic

open ResidueDial

variable (p : ℕ) [Fact p.Prime]

/-- The quadratic character of `ZMod p`, valued in `ℂ`. -/
noncomputable def quadCharC : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)











end Price2Adic


