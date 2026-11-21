-- Prove2me | Theorems.Thm_Kourovka_FinitePaths_factorial_middle_eq_terminal_of_bounded_prefixes
-- name    : Kourovka.FinitePaths.factorial_middle_eq_terminal_of_bounded_prefixes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:52.332113+00:00
-- url     : https://prove2.me/theorems/25113302-d63e-4b44-8dc1-2ffeb0a7c2c6
-- title:
--   Finite Paths: factorial middle eq terminal of bounded prefixes
-- statement:
--   The factorial bound depends only on the number of possible prefixes, not on the shift.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L149-L173
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L149-L173

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

theorem Kourovka.FinitePaths.factorial_middle_eq_terminal_of_bounded_prefixes {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b)
    (hs : ∀ x ∈ X, shift x ∈ X) :
    ∀ x ∈ X, x b.factorial = x (2 * b.factorial) := by sorry
