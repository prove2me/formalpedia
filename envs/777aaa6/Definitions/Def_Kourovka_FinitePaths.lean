-- Prove2me | Definitions.Def_Kourovka_FinitePaths
-- name    : Kourovka_FinitePaths
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:27:45.007342+00:00
-- url     : https://prove2.me/theorems/b5b95c61-098c-4098-9249-0c4929f9fba8
-- title:
--   Finite Paths
-- statement:
--   Definitions and structural lemmas for Finite Paths, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/FinitePaths.lean

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit true
namespace Kourovka
namespace FinitePaths
def initialSegment {α : Type*} (n : ℕ) (x : ℕ → α) : Fin n → α := fun i => x i
def shift {α : Type*} (x : ℕ → α) : ℕ → α := fun n => x (n + 1)
end FinitePaths
end Kourovka


