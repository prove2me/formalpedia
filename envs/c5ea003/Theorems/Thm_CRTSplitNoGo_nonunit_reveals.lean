-- Prove2me | Theorems.Thm_CRTSplitNoGo_nonunit_reveals
-- name    : CRTSplitNoGo.nonunit_reveals
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:37:45.878795+00:00
-- url     : https://prove2.me/theorems/874ae954-5064-408a-b669-a706368394f8
-- title:
--   A non-unit is a factorisation.
-- statement:
--   **A non-unit is a factorisation.**  If `v : ZMod N` is neither `0` nor invertible then the
--   integer `v.val` reveals a nontrivial factor of `N`.  Division is thus the only way for a
--   straight-line program to leave the polynomial world, and it can only do so by producing the
--   factorisation it was supposed to compute (barrier 6).
--
--   ```lean
--   theorem CRTSplitNoGo.nonunit_reveals{N : ℕ} (hN : 1 < N) (v : ZMod N) (hv0 : v ≠ 0) (hvu : ¬ IsUnit v) :
--       RevealsFactor N (v.val : ℤ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGoStraightLine.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGoStraightLine.lean#L252

-- Thm stub generated from Bridges/CRTSplitNoGoStraightLine.lean
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

theorem CRTSplitNoGo.nonunit_reveals{N : ℕ} (hN : 1 < N) (v : ZMod N) (hv0 : v ≠ 0) (hvu : ¬ IsUnit v) :
    RevealsFactor N (v.val : ℤ) := by sorry
