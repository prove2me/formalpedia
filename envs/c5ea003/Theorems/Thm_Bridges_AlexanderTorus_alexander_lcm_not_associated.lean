-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_lcm_not_associated
-- name    : Bridges.AlexanderTorus.alexander_lcm_not_associated
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:18:04.137454+00:00
-- url     : https://prove2.me/theorems/15f4a777-5aac-454a-b82f-8b6780c7d5d8
-- title:
--   No join morphism.
-- statement:
--   **No join morphism.** `lcm(A_3, A_5)` is *not* associated to `A_{lcm(3,5)} = A_{15}`:
--   the former has degree `6` (it is `Φ_6 · Φ_10`), the latter degree `14` (it also contains
--   the factor `Φ_30`).  This refutes the lcm half of the lattice conjecture.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_lcm_not_associated:
--       ¬ Associated (lcm (alexander 3) (alexander 5)) (alexander (Nat.lcm 3 5)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeVII.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeVII.lean#L137

-- Thm stub generated from Bridges/AlexanderKnotNumberBridgeVII.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeVII
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

open Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The divisor-product formula, including `N = 1` -/






/-! ## The two excesses share no irreducible factor -/


/-! ## The gcd half of the lattice conjecture: true -/



/-! ## The lcm half of the lattice conjecture: false -/

theorem Bridges.AlexanderTorus.alexander_lcm_not_associated:
    ¬ Associated (lcm (alexander 3) (alexander 5)) (alexander (Nat.lcm 3 5)) := by sorry
