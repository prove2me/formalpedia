-- Prove2me | solution 1 for CRTSplitNoGo.nonunit_reveals
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:58:00.683474+00:00
-- url     : https://prove2.me/submissions/4820fd20-a09c-4165-b5d3-f81c34ed5e8f

-- Sol generated from Bridges/CRTSplitNoGoStraightLine.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Definitions.Def_Bridges_CRTSplitNoGoStraightLine

/-!
# The CRT-Split No-Go, Part X: the straight-line rigidity dichotomy

Parts I–II proved Fact 2 for *polynomial* maps.  Conjecture A of the previous cycle asked for
the general form: let `F` be any function computed by a straight-line program over `ZMod N`
with the operations `+`, `−`, `×`, division, and constants read off `N`.  Then either `F` is
CRT-blind — the same program computes both reduced components, so no information about the
splitting `N = p q` is produced — or the program hits, at some intermediate node, a value that
is **not invertible mod `N`**, and such a value either vanishes or *is* a factorisation.

This file proves that dichotomy.

## The formalisation

`SLE` is the type of straight-line expressions in one variable: a variable node, integer
constants (the "digits of `N`" of the informal statement — any integers at all, so the theorem
is stronger), the ring operations, and an inversion node.  `SLE.eval` interprets an expression
in an arbitrary commutative ring, an inversion node being `Ring.inverse` (which returns `0` on
a non-unit).  `SLE.AllUnits e x` says that every inversion node of `e` is applied to a unit at
input `x`; `SLE.DivFree e` says there is no inversion node at all.

## Main results

* `SLE.eval_hom` — **CRT-blindness.**  If all inversions succeed, evaluation commutes with any
  ring homomorphism: `φ (eval e x) = eval e (φ x)`.  `SLE.eval_hom_of_divFree` is the
  division-free case, where no hypothesis is needed.
* `SLE.toPoly` / `SLE.eval_toPoly` — a division-free program is literally an integer
  polynomial, so every theorem of Parts I–V applies to it verbatim
  (`slp_reveal_iff_xor_closure`).
* `slpOrbit_crt` — the orbit of an `SLE`-iteration in `ZMod (p q)` maps, under the Chinese
  remainder isomorphism, to the pair of orbits of *the same* program in `ZMod p` and `ZMod q`.
  This is the exact sense in which an `N`-explicit map "does not split the CRT".
* `nonunit_reveals` — **the escape is a factorisation.**  A value of `ZMod N` that is neither
  zero nor a unit yields `RevealsFactor N`.
* `sle_dichotomy` — the two together: for every straight-line program and every input, either
  the computation is CRT-blind, or some intermediate value hands you a nontrivial factor of `N`
  (or is zero).  Escaping polynomiality by dividing therefore *presupposes* the factorisation:
  this is barrier 6 (circularity), now for arbitrary straight-line programs rather than for
  idempotents alone.
-/

open CRTSplitNoGo

/-! ## Straight-line expressions -/


open SLE






/-! ## Ring homomorphisms commute with successful straight-line computation -/




/-! ## Division-free programs are exactly polynomials -/

open Polynomial




/-! ## Straight-line iteration -/








/-! ## The escape from polynomiality is a factorisation -/



/-! ## Instances of the dichotomy on the CTST demo modulus -/







open CRTSplitNoGo in
theorem solution{N : ℕ} (hN : 1 < N) (v : ZMod N) (hv0 : v ≠ 0) (hvu : ¬ IsUnit v) :
    RevealsFactor N (v.val : ℤ) := by
  haveI : NeZero N := ⟨by omega⟩
  have hval_lt : v.val < N := ZMod.val_lt v
  have hval_ne : v.val ≠ 0 := (ZMod.val_ne_zero v).mpr hv0
  have hcast : ((v.val : ℕ) : ZMod N) = v := ZMod.natCast_val v |>.trans (ZMod.cast_id N v)
  have hcop : ¬ Nat.Coprime v.val N := by
    intro hc
    exact hvu (by rw [← hcast]; exact (ZMod.isUnit_iff_coprime v.val N).mpr hc)
  have hgcd : Int.gcd (v.val : ℤ) (N : ℤ) = Nat.gcd v.val N := Int.gcd_natCast_natCast _ _
  refine ⟨?_, ?_⟩
  · rw [hgcd]
    have hne1 : Nat.gcd v.val N ≠ 1 := hcop
    have hpos : 0 < Nat.gcd v.val N := Nat.gcd_pos_of_pos_right _ (by omega)
    omega
  · rw [hgcd]
    have hdvd : Nat.gcd v.val N ∣ v.val := Nat.gcd_dvd_left _ _
    have hle : Nat.gcd v.val N ≤ v.val := Nat.le_of_dvd (by omega) hdvd
    omega
