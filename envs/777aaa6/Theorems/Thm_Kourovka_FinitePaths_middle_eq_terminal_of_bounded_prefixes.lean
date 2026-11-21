-- Prove2me | Theorems.Thm_Kourovka_FinitePaths_middle_eq_terminal_of_bounded_prefixes
-- name    : Kourovka.FinitePaths.middle_eq_terminal_of_bounded_prefixes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:37:35.599797+00:00
-- url     : https://prove2.me/theorems/45e54d05-77bb-4340-8e9d-119691a811e3
-- title:
--   Finite Paths: middle eq terminal of bounded prefixes
-- statement:
--   Bounded path branching and shift closure give the common middle-to-terminal index identity.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L141-L146
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L141-L146

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

theorem Kourovka.FinitePaths.middle_eq_terminal_of_bounded_prefixes {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b)
    (hs : ∀ x ∈ X, shift x ∈ X) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ X, x m = x (2 * m) := by sorry
