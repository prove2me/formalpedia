-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_lcm_natDegree_add_defect
-- name    : Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:17:56.902815+00:00
-- url     : https://prove2.me/theorems/9594adb8-972e-4db6-b78a-cea1ebdd7e9d
-- title:
--   Quantitative failure of the join morphism.
-- statement:
--   **Quantitative failure of the join morphism.**  The degree gap between `A_{lcm(M,N)}` and
--   `lcm(A_M, A_N)` is exactly `∑ φ(d)` over the divisors `d > 1` of `lcm(M,N)` that divide
--   neither `M` nor `N`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect{M N : ℕ} (hM : Odd M) (hN : Odd N)
--       (hMpos : 0 < M) (hNpos : 0 < N) :
--       (alexander (Nat.lcm M N)).natDegree
--         = (lcm (alexander M) (alexander N)).natDegree
--           + ∑ d ∈ ((Nat.lcm M N).divisors.erase 1) \ unionIdx M N, Nat.totient d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeXI.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeXI.lean#L185

-- Thm stub generated from Bridges/AlexanderKnotNumberBridgeXI.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeVII
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXI
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

open Bridges.AlexanderTorus

open Polynomial Finset

/-! ## Divisor sets of gcd's and lcm's -/







/-! ## The join on the polynomial side -/


/-! ## The join defect -/





/-! ## Degrees -/

theorem Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect{M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) :
    (alexander (Nat.lcm M N)).natDegree
      = (lcm (alexander M) (alexander N)).natDegree
        + ∑ d ∈ ((Nat.lcm M N).divisors.erase 1) \ unionIdx M N, Nat.totient d := by sorry
