-- Prove2me | Theorems.Thm_Kourovka_FinitePaths_exists_injective_prefix
-- name    : Kourovka.FinitePaths.exists_injective_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:28:18.171867+00:00
-- url     : https://prove2.me/theorems/d25c799d-6992-456c-a7bc-43ce7e68d808
-- title:
--   Finite Paths: exists injective prefix
-- statement:
--   A finite family of distinct infinite sequences is separated by some finite prefix.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L20-L37
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L20-L37

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

theorem Kourovka.FinitePaths.exists_injective_prefix {α ι : Type*} [Fintype ι]
    (f : ι → ℕ → α) (hf : Function.Injective f) :
    ∃ n, Function.Injective (fun i => initialSegment n (f i)) := by sorry
