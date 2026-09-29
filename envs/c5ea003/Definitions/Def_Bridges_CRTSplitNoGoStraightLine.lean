-- Prove2me | Definitions.Def_Bridges_CRTSplitNoGoStraightLine
-- name    : Bridges_CRTSplitNoGoStraightLine
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:37.271654+00:00
-- url     : https://prove2.me/theorems/648a58cf-555b-4462-ae6f-9c1f90e05c09
-- title:
--   Aether Catalog definitions — Bridges_CRTSplitNoGoStraightLine
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CRTSplitNoGoStraightLine`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CRTSplitNoGoStraightLine.lean by skeleton subtraction
import Mathlib

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

namespace CRTSplitNoGo

/-! ## Straight-line expressions -/

/-- A straight-line expression in one variable: constants, the ring operations, and
inversion. -/
inductive SLE : Type
  | var : SLE
  | const : ℤ → SLE
  | add : SLE → SLE → SLE
  | sub : SLE → SLE → SLE
  | mul : SLE → SLE → SLE
  | inv : SLE → SLE
  deriving DecidableEq

namespace SLE

/-- Interpretation of a straight-line expression in a commutative ring; an inversion node is
`Ring.inverse`, which is the true inverse on units and `0` elsewhere. -/
noncomputable def eval {R : Type*} [CommRing R] : SLE → R → R
  | var, x => x
  | const c, _ => (c : R)
  | add a b, x => eval a x + eval b x
  | sub a b, x => eval a x - eval b x
  | mul a b, x => eval a x * eval b x
  | inv a, x => Ring.inverse (eval a x)

/-- Every inversion node of the expression is applied to a unit at the given input. -/
def AllUnits {R : Type*} [CommRing R] : SLE → R → Prop
  | var, _ => True
  | const _, _ => True
  | add a b, x => AllUnits a x ∧ AllUnits b x
  | sub a b, x => AllUnits a x ∧ AllUnits b x
  | mul a b, x => AllUnits a x ∧ AllUnits b x
  | inv a, x => AllUnits a x ∧ IsUnit (eval a x)

/-- The expression contains no inversion node. -/
def DivFree : SLE → Prop
  | var => True
  | const _ => True
  | add a b => DivFree a ∧ DivFree b
  | sub a b => DivFree a ∧ DivFree b
  | mul a b => DivFree a ∧ DivFree b
  | inv _ => False



/-! ## Ring homomorphisms commute with successful straight-line computation -/




/-! ## Division-free programs are exactly polynomials -/

open Polynomial

/-- The integer polynomial computed by a division-free straight-line expression. -/
noncomputable def toPoly : SLE → ℤ[X]
  | var => X
  | const c => C c
  | add a b => toPoly a + toPoly b
  | sub a b => toPoly a - toPoly b
  | mul a b => toPoly a * toPoly b
  | inv _ => 0


end SLE

/-! ## Straight-line iteration -/

/-- The orbit of a straight-line program iterated in a commutative ring. -/
noncomputable def slpOrbit {R : Type*} [CommRing R] (e : SLE) (x0 : R) (n : ℕ) : R :=
  (fun z => SLE.eval e z)^[n] x0







/-! ## The escape from polynomiality is a factorisation -/



/-! ## Instances of the dichotomy on the CTST demo modulus -/

/-- The straight-line program computing the CTST map `x ↦ x² + 1`. -/
def sleSq : SLE := SLE.add (SLE.mul SLE.var SLE.var) (SLE.const 1)





end CRTSplitNoGo


