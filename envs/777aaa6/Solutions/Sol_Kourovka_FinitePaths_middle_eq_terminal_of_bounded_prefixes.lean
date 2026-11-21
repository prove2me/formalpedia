-- Prove2me | solution 1 for Kourovka.FinitePaths.middle_eq_terminal_of_bounded_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:37.754798+00:00
-- url     : https://prove2.me/submissions/acf1c15e-fa44-41f4-babb-4d781f80cd96

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_FinitePaths
import Theorems.Thm_Kourovka_FinitePaths_finite_of_bounded_prefixes
import Theorems.Thm_Kourovka_FinitePaths_middle_eq_terminal

set_option autoImplicit true
open Kourovka
open Kourovka.FinitePaths
namespace Kourovka.FinitePaths
theorem _root_.solution {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b)
    (hs : ∀ x ∈ X, shift x ∈ X) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ X, x m = x (2 * m) :=
  middle_eq_terminal X (finite_of_bounded_prefixes X b hb) hs
end Kourovka.FinitePaths
