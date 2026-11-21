-- Prove2me | Theorems.Thm_Kourovka_FinitePaths_finite_of_bounded_prefixes
-- name    : Kourovka.FinitePaths.finite_of_bounded_prefixes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:28:12.333175+00:00
-- url     : https://prove2.me/theorems/af72c576-1c8c-434a-b35d-4a0fd361d352
-- title:
--   Finite Paths: finite of bounded prefixes
-- statement:
--   Uniformly bounded prefix sets allow only finitely many infinite sequences.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L40-L56
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean#L40-L56

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

theorem Kourovka.FinitePaths.finite_of_bounded_prefixes {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b) : X.Finite := by sorry
