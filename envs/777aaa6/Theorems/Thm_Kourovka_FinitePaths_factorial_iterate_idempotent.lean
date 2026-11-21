-- Prove2me | Theorems.Thm_Kourovka_FinitePaths_factorial_iterate_idempotent
-- name    : Kourovka.FinitePaths.factorial_iterate_idempotent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:28:22.252467+00:00
-- url     : https://prove2.me/theorems/5295c0f0-5e10-42a6-bea0-88c1caff128b
-- title:
--   Finite Paths: factorial iterate idempotent
-- statement:
--   The factorial of a cardinality bound is an idempotent exponent for every endomap.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L71-L104
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L71-L104

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_FinitePaths
set_option autoImplicit true
open Kourovka
open Kourovka.FinitePaths

theorem Kourovka.FinitePaths.factorial_iterate_idempotent {X : Type*} [Fintype X]
    (f : X → X) (b : ℕ) (hcard : Fintype.card X ≤ b) :
    f^[2 * b.factorial] = f^[b.factorial] := by sorry
