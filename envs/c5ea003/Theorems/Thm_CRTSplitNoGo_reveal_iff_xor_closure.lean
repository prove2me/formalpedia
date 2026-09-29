-- Prove2me | Theorems.Thm_CRTSplitNoGo_reveal_iff_xor_closure
-- name    : CRTSplitNoGo.reveal_iff_xor_closure
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:37:08.272326+00:00
-- url     : https://prove2.me/theorems/a6089c92-7c5b-4729-adb2-972cac829ed8
-- title:
--   The reveal characterisation.
-- statement:
--   **The reveal characterisation.**  Along the orbit of *any* integer polynomial map,
--   `gcd (x t - x s) N` is a nontrivial factor of `N = p * q` if and only if the mod-`p` orbit
--   closes up between times `s` and `t` **exclusive-or** the mod-`q` orbit does.
--
--   ```lean
--   theorem CRTSplitNoGo.reveal_iff_xor_closure{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
--       (f : ℤ[X]) (x0 : ℤ) (s t : ℕ) :
--       RevealsFactor (p * q) (polyOrbit f x0 t - polyOrbit f x0 s) ↔
--         Xor' (modOrbit f p x0 t = modOrbit f p x0 s)
--              (modOrbit f q x0 t = modOrbit f q x0 s) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGo.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGo.lean#L167

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









/-! ## Consequence: the reveal event is an exclusive mod-`p` cycle closure -/

theorem CRTSplitNoGo.reveal_iff_xor_closure{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (f : ℤ[X]) (x0 : ℤ) (s t : ℕ) :
    RevealsFactor (p * q) (polyOrbit f x0 t - polyOrbit f x0 s) ↔
      Xor' (modOrbit f p x0 t = modOrbit f p x0 s)
           (modOrbit f q x0 t = modOrbit f q x0 s) := by sorry
