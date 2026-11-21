-- Prove2me | Theorems.Thm_Kourovka_FinitePaths_ncard_le_of_bounded_prefixes
-- name    : Kourovka.FinitePaths.ncard_le_of_bounded_prefixes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:36.481883+00:00
-- url     : https://prove2.me/theorems/d1423c82-1d29-472f-856b-ec290ea1be2c
-- title:
--   Finite Paths: ncard le of bounded prefixes
-- statement:
--   A bound on all prefix sets also bounds the number of infinite sequences.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L59-L68
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L59-L68

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

theorem Kourovka.FinitePaths.ncard_le_of_bounded_prefixes {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b) : X.ncard ≤ b := by sorry
