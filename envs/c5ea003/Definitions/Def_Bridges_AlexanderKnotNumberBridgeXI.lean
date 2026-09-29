-- Prove2me | Definitions.Def_Bridges_AlexanderKnotNumberBridgeXI
-- name    : Bridges_AlexanderKnotNumberBridgeXI
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:37.945006+00:00
-- url     : https://prove2.me/theorems/7b947f2e-dadb-4790-b1ba-3e4b67c4355e
-- title:
--   Aether Catalog definitions — Bridges_AlexanderKnotNumberBridgeXI
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlexanderKnotNumberBridgeXI`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlexanderKnotNumberBridgeXI.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeVII
/-
# The knot–number bridge XI: the join defect

Cycle VII proved that `N ↦ A_N` is a **meet**-morphism of the divisor lattice
(`alexander_gcd`) but *not* a join-morphism (`alexander_lcm_not_associated`).  Conjecture
`D1` of `FUTURE_DIRECTIONS.md` asked for the exact size of the failure.  This file closes it.

* `Bridges.AlexanderTorus.alexander_lcm_eq_joinProd` : for odd `M, N > 0`,
  `lcm(A_M, A_N)` is associated to `∏_{d ∣ M or d ∣ N, d > 1} Φ_{2d}` — the join on the
  polynomial side is the product over the *union* of the two divisor sets, whereas
  `A_{lcm(M,N)}` is the product over the divisor set of `lcm(M,N)`, which is generally larger.
* `Bridges.AlexanderTorus.alexander_lcm_mul_joinDefect` : the missing factor is exactly
  `∏_{d ∣ lcm(M,N), d ∤ M, d ∤ N, d > 1} Φ_{2d}`, and
  `Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect` measures it:
  `deg A_{lcm(M,N)} = deg lcm(A_M, A_N) + ∑_{d} φ(d)` over that same index set.
* `Bridges.AlexanderTorus.joinDefect_isUnit_iff` : the join morphism property holds at
  `(M, N)` precisely when `lcm(M,N)` has no divisor `> 1` outside `divisors M ∪ divisors N`.
* `Bridges.AlexanderTorus.joinDefect_three_five_natDegree` : the numerical instance behind
  cycle VII's counterexample — the defect for `(3,5)` is `Φ_30`, of degree `φ(15) = 8`,
  and indeed `14 = 6 + 8`.

Everything reduces, as predicted, to the Finset identity
`(∏_{s ∪ t}) · (∏_{s ∩ t}) = (∏_s) · (∏_t)` together with `divisors (gcd M N) =
divisors M ∩ divisors N`.
-/

namespace Bridges.AlexanderTorus

open Polynomial Finset

/-! ## Divisor sets of gcd's and lcm's -/


/-- The index set of the join: the nontrivial divisors of `M` together with those of `N`. -/
def unionIdx (M N : ℕ) : Finset ℕ := (M.divisors ∪ N.divisors).erase 1


/-- The cyclotomic product over the union of the two divisor sets. -/
noncomputable def joinProd (M N : ℕ) : ℤ[X] :=
  ∏ d ∈ unionIdx M N, cyclotomic (2 * d) ℤ



/-! ## The join on the polynomial side -/


/-! ## The join defect -/

/-- The join defect: the cyclotomic factors of `A_{lcm(M,N)}` that are visible at neither
`M` nor `N`. -/
noncomputable def joinDefect (M N : ℕ) : ℤ[X] :=
  ∏ d ∈ ((Nat.lcm M N).divisors.erase 1) \ unionIdx M N, cyclotomic (2 * d) ℤ




/-! ## Degrees -/






/-! ## The numerical instance behind cycle VII's counterexample -/


end Bridges.AlexanderTorus


