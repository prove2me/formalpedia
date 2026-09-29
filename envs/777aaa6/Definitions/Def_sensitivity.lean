-- Prove2me | Definitions.Def_sensitivity
-- name    : sensitivity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-04-24T03:36:19.589394+00:00
-- url     : https://prove2.me/theorems/30247bb9-3fe7-4b5c-8fec-e04586e1ad40
-- statement:
--   Cook–Dwork–Reischuk sensitivity `s(f)` of a Boolean function and its pointwise `s(f,x)`.

import Definitions.Def_BoolFunc
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi

/-!
# Sensitivity of a Boolean function

Cook–Dwork–Reischuk's pointwise sensitivity, and its global maximum.
-/

/-- Flip the `i`-th bit of `x`. -/
def flipBit {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

/-- Pointwise sensitivity `s(f, x)`: number of neighbors of `x` on which `f`
    disagrees with `f x`. -/
def sensitivityAt {n : ℕ} (f : BoolFunc n) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => f (flipBit x i) ≠ f x)).card

/-- Sensitivity `s(f)`: maximum pointwise sensitivity over the cube. -/
def sensitivity {n : ℕ} (f : BoolFunc n) : ℕ :=
  Finset.univ.sup (sensitivityAt f)


