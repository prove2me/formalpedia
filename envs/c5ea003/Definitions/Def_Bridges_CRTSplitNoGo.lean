-- Prove2me | Definitions.Def_Bridges_CRTSplitNoGo
-- name    : Bridges_CRTSplitNoGo
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:34.525292+00:00
-- url     : https://prove2.me/theorems/a4404211-2dee-4fa4-82af-827156b2c5ff
-- title:
--   Aether Catalog definitions — Bridges_CRTSplitNoGo
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CRTSplitNoGo`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CRTSplitNoGo.lean by skeleton subtraction
import Mathlib

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

namespace CRTSplitNoGo

open Polynomial

/-! ## Fact 1: a nontrivial gcd is exactly an exclusive CRT collision -/

/-- `d` reveals a nontrivial factor of `N`: `gcd d N` is neither `1` nor `N`. -/
def RevealsFactor (N : ℕ) (d : ℤ) : Prop :=
  1 < Int.gcd d (N : ℤ) ∧ Int.gcd d (N : ℤ) < N



/-! ## Fact 2: an `N`-explicit map is functorial for reduction mod `p` -/

/-- The orbit of the seed `x₀` under the integer polynomial map `f`. -/
def polyOrbit (f : ℤ[X]) (x0 : ℤ) (n : ℕ) : ℤ := (fun z => f.eval z)^[n] x0



/-- The orbit of the reduced seed under the reduced polynomial map, in `ZMod m`. -/
noncomputable def modOrbit (f : ℤ[X]) (m : ℕ) (x0 : ℤ) (n : ℕ) : ZMod m :=
  (fun z => (f.map (Int.castRingHom (ZMod m))).eval z)^[n] ((x0 : ℤ) : ZMod m)





/-! ## Consequence: the reveal event is an exclusive mod-`p` cycle closure -/




/-! ## The rho shape: closures exist, but pigeonhole only gives `t ≤ p` -/



end CRTSplitNoGo


