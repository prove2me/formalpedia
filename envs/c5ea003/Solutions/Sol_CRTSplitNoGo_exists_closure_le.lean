-- Prove2me | solution 1 for CRTSplitNoGo.exists_closure_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:57:59.068634+00:00
-- url     : https://prove2.me/submissions/a1053414-835a-484c-ab57-ac46cad05d18

-- Sol generated from Bridges/CRTSplitNoGo.lean
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




/-! ## The rho shape: closures exist, but pigeonhole only gives `t ≤ p` -/




open CRTSplitNoGo in
theorem solution(f : ℤ[X]) (m : ℕ) [NeZero m] (x0 : ℤ) :
    ∃ s t, s < t ∧ t ≤ m ∧ modOrbit f m x0 t = modOrbit f m x0 s := by
  have hcard : Fintype.card (ZMod m) < Fintype.card (Fin (m + 1)) := by
    simp [ZMod.card m]
  obtain ⟨i, j, hij, hval⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (m + 1) => modOrbit f m x0 (i : ℕ)) hcard
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with h | h
  · exact ⟨i, j, h, by omega, hval.symm⟩
  · exact ⟨j, i, h, by omega, hval⟩
