-- Prove2me | Theorems.Thm_Kourovka_FinitePaths_exists_idempotent_iterate
-- name    : Kourovka.FinitePaths.exists_idempotent_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:28:08.775354+00:00
-- url     : https://prove2.me/theorems/d31ffec0-5cb6-4713-8f28-2bf448970df2
-- title:
--   Finite Paths: exists idempotent iterate
-- statement:
--   Every endomap of a finite set has an idempotent positive iterate.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L107-L112
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L107-L112

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

theorem Kourovka.FinitePaths.exists_idempotent_iterate {X : Type*} [Finite X] (f : X → X) :
    ∃ m : ℕ, 0 < m ∧ f^[2 * m] = f^[m] := by sorry
