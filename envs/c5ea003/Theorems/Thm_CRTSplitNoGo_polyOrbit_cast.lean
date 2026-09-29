-- Prove2me | Theorems.Thm_CRTSplitNoGo_polyOrbit_cast
-- name    : CRTSplitNoGo.polyOrbit_cast
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:37:02.022259+00:00
-- url     : https://prove2.me/theorems/cd38ecb8-2da5-4702-9b72-06fd44bde729
-- title:
--   Fact 2 (functoriality).
-- statement:
--   **Fact 2 (functoriality).** Reducing the integer orbit mod `m` gives the orbit of the
--   reduced polynomial: the mod-`m` dynamics is computed entirely inside `ZMod m`.
--
--   ```lean
--   theorem CRTSplitNoGo.polyOrbit_cast(f : ℤ[X]) (m : ℕ) (x0 : ℤ) (n : ℕ) :
--       ((polyOrbit f x0 n : ℤ) : ZMod m) = modOrbit f m x0 n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGo.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGo.lean#L130

-- Thm stub generated from Bridges/CRTSplitNoGo.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo

/-!
# The CRT-Split No-Go, Part I: the reveal mechanism

This file formalises the two structural facts underlying the claim that no classical
iteration built from `N` alone can factor `N = p * q` in `poly(log N)` steps.

* **Fact 1 (CRT-split collision is the only reveal mechanism).**
  For `N = p * q` with `p ≠ q` prime and any integer `d`,
  `gcd d N` is a *nontrivial* divisor of `N` if and only if **exactly one** of
  `p ∣ d`, `q ∣ d` holds (`crt_reveal_iff`).  Applied to `d = x t - x s` along a
  trajectory this says: a factor appears exactly when two trajectory values agree
  on **one** CRT component.

* **Fact 2 (`N`-explicit maps do not split the CRT).**
  An `N`-explicit map is a polynomial with integer coefficients (ring operations and
  constants manufactured from the digits of `N`).  Its orbit reduced mod `p` is the
  orbit of the *reduced* polynomial started at the *reduced* seed
  (`polyOrbit_cast`, `modOrbit_congr`): the mod-`p` dynamics depends on nothing
  except `f mod p` and `x₀ mod p`.  In particular the map itself carries no
  information about which of the two CRT components it is being run in.

* **Consequence.** The factor-revealing event in any such iteration is *exactly* an
  exclusive mod-`p` / mod-`q` cycle closure (`reveal_iff_xor_closure`), and no reveal
  can happen before the first closure (`no_reveal_before_closure`).  Closures do
  exist, but the only unconditional guarantee is the pigeonhole bound `t ≤ p`
  (`exists_closure_le`), and after a closure the orbit is eventually periodic
  (`modOrbit_eventually_periodic`) — the rho shape.

Quantitative lower bounds for the three regimes are in `CRTSplitNoGoBounds.lean`.
-/

open CRTSplitNoGo

open Polynomial

/-! ## Fact 1: a nontrivial gcd is exactly an exclusive CRT collision -/




/-! ## Fact 2: an `N`-explicit map is functorial for reduction mod `p` -/

theorem CRTSplitNoGo.polyOrbit_cast(f : ℤ[X]) (m : ℕ) (x0 : ℤ) (n : ℕ) :
    ((polyOrbit f x0 n : ℤ) : ZMod m) = modOrbit f m x0 n := by sorry
