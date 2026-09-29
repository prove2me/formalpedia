-- Prove2me | Definitions.Def_Bridges_AlexanderKnotNumberBridgeVII
-- name    : Bridges_AlexanderKnotNumberBridgeVII
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:59.527302+00:00
-- url     : https://prove2.me/theorems/9877e161-8e2f-40b0-bc76-ff2c342bb188
-- title:
--   Aether Catalog definitions — Bridges_AlexanderKnotNumberBridgeVII
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlexanderKnotNumberBridgeVII`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlexanderKnotNumberBridgeVII.lean by skeleton subtraction
import Mathlib
/-
# The knot–number bridge VII: the divisor lattice, gcd's and the failure of lcm's

Cycle III proved the *poset* statement `A_d ∣ A_M ↔ d ∣ M` and cycle IV the coprimality
statement "all common divisors of `A_M`, `A_N` are units iff `gcd(M,N) = 1`".  Conjecture `C4`
of `FUTURE_DIRECTIONS.md` asked whether `N ↦ A_N` is a lattice map, i.e. whether
`gcd(A_M, A_N) ≐ A_{gcd(M,N)}` **and** `lcm(A_M, A_N) ≐ A_{lcm(M,N)}`.

This file settles both halves:

* `Bridges.AlexanderTorus.alexander_gcd` : the gcd half is **true** — for odd `M, N > 0`,
  `gcd(A_M, A_N)` is associated to `A_{gcd(M,N)}` in `ℤ[X]`, with the universal-property
  form `alexander_dvd_gcd_of_dvd_of_dvd`.
* `Bridges.AlexanderTorus.alexander_lcm_not_associated` : the lcm half is **false** — already
  `lcm(A_3, A_5)` has degree `6` while `A_{15}` has degree `14`, so the map `N ↦ A_N` is a
  meet-morphism but not a join-morphism of the divisor lattice.

The mechanism behind the gcd half is that `A_M` is a product of *distinct* cyclotomic primes
`Φ_{2d}`, `d ∣ M`, `d > 1`, so the "excess" parts of `A_M` and `A_N` over `A_{gcd(M,N)}`
share no irreducible factor; the mechanism behind the failure of the lcm half is that
`A_{lcm(M,N)}` also contains the factors `Φ_{2d}` for divisors `d` of `lcm(M,N)` that divide
neither `M` nor `N`.
-/

namespace Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The divisor-product formula, including `N = 1` -/



/-- The "excess" factor of `A_M` over `A_G` for a divisor `G ∣ M`. -/
noncomputable def excess (G M : ℕ) : ℤ[X] :=
  ∏ d ∈ (M.divisors.erase 1) \ (G.divisors.erase 1), cyclotomic (2 * d) ℤ



/-! ## The two excesses share no irreducible factor -/


/-! ## The gcd half of the lattice conjecture: true -/



/-! ## The lcm half of the lattice conjecture: false -/




end Bridges.AlexanderTorus


