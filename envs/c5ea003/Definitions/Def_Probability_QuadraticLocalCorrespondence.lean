-- Prove2me | Definitions.Def_Probability_QuadraticLocalCorrespondence
-- name    : Probability_QuadraticLocalCorrespondence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:27.855367+00:00
-- url     : https://prove2.me/theorems/f7f6faeb-08f4-4eb1-a7be-419b00eeae5d
-- title:
--   Aether Catalog definitions — Probability_QuadraticLocalCorrespondence
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.QuadraticLocalCorrespondence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/QuadraticLocalCorrespondence.lean by skeleton subtraction
import Mathlib
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Quadratic local correspondence: ramification and Legendre colors

For a quadratic discriminant `D` and a rational prime `p`, the quadratic character has
local value `χ_D(p) = (D/p)`.  This file proves, uniformly in `D` and `p`, the elementary
local dictionary behind the degree-two case:

* value `0` exactly at ramified primes (`p ∣ D`);
* away from ramification the value is one of `±1` and has square `1`;
* value `1` exactly when `D` is a square modulo `p`;
* value `-1` exactly when `D` is a nonsquare modulo `p`;
* these facts combine into a three-way ramified/split/inert classification.

This is the rigorously accessible local arithmetic core of the proposed test.  It does not
claim to formalize the global Langlands correspondence or enumerate quadratic fields.
-/

namespace LanglandsForToddlers

/-- The local quadratic color attached to an integer `D` at a prime `p`. -/
def quadraticColor (D : ℤ) (p : ℕ) [Fact p.Prime] : ℤ := legendreSym p D

/-
The local color vanishes exactly when the prime ramifies (divides `D`).
-/

/-
At an unramified prime, a quadratic color is exactly one of the two signs.
-/

/-
Every unramified quadratic color has order dividing two.
-/

/-
The complete ramified/unramified numerical packet for a local quadratic color.
-/

/-
At an unramified prime, color `1` is precisely the split (square-residue) case.
-/

/-
Color `-1` is precisely the inert (nonsquare-residue) case.
-/

/-
The local shape-color dictionary, packaged as a three-way classification.

The three alternatives correspond to ramified, split, and inert behavior respectively.
This final result uses the preceding nonsquare characterization and the local packet.
-/

end LanglandsForToddlers


