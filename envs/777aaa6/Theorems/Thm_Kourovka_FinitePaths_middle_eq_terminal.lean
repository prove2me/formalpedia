-- Prove2me | Theorems.Thm_Kourovka_FinitePaths_middle_eq_terminal
-- name    : Kourovka.FinitePaths.middle_eq_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:49.772191+00:00
-- url     : https://prove2.me/theorems/6212a2f6-33e8-4d0c-8249-52d3142a82b2
-- title:
--   Finite Paths: middle eq terminal
-- statement:
--   A finite shift-closed family has one common eventual period.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L118-L138
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L118-L138

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

theorem Kourovka.FinitePaths.middle_eq_terminal {α : Type*} (X : Set (ℕ → α)) (hX : X.Finite)
    (hs : ∀ x ∈ X, shift x ∈ X) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ X, x m = x (2 * m) := by sorry
