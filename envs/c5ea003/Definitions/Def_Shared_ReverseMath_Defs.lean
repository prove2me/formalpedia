-- Prove2me | Definitions.Def_Shared_ReverseMath_Defs
-- name    : Shared_ReverseMath_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:12:41.136285+00:00
-- url     : https://prove2.me/theorems/ef9ebc31-da96-403f-8b62-6a4337b3a643
-- title:
--   Aether Catalog definitions — Shared_ReverseMath_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ReverseMath.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ReverseMath/Defs.lean by skeleton subtraction
import Mathlib
/-
# Reverse Mathematics: Basic Definitions for Ramsey-Theoretic Principles

This module fixes the combinatorial vocabulary used throughout the reverse
mathematics development of Ramsey's theorem for pairs.  It introduces the
symmetric two-colourings of pairs of natural numbers, homogeneous sets, and the
statements `RT¹₂`, `RT¹ₖ`, `RT²₂`, `SRT²₂`, and `COH` whose implications are
studied in `Shared.ReverseMath.Implications`.
-/

open Set

/-- A symmetric two-colouring of unordered pairs of natural numbers. -/
structure PairColoring where
  /-- The colour assigned to the pair `{i, j}` (recorded on the ordered pair). -/
  color : ℕ → ℕ → Bool
  /-- The colour depends only on the unordered pair. -/
  symm : ∀ i j, color i j = color j i

/-- A set `S` is *homogeneous* of colour `b` for a pair colouring `c` if it is
infinite and every pair of distinct elements of `S` receives colour `b`. -/
def IsHomogeneous (S : Set ℕ) (c : PairColoring) (b : Bool) : Prop :=
  S.Infinite ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c.color i j = b

/-- The canonical pair colouring induced by a unary colouring `f`:
`c(i, j) = f(min i j)`.  This is the reduction used to derive `RT¹₂` from the
pair versions. -/
def pairColoringOfUnary (f : ℕ → Bool) : PairColoring where
  color i j := f (min i j)
  symm i j := by rw [min_comm]

/-- **RT¹₂**: every two-colouring of `ℕ` has an infinite monochromatic class. -/
def RT1_2_Bool : Prop :=
  ∀ f : ℕ → Bool, ∃ b : Bool, (f ⁻¹' {b}).Infinite

/-- **RT¹ₖ**: every `k`-colouring of `ℕ` has an infinite monochromatic class. -/
def RT1_k (k : ℕ) : Prop :=
  ∀ f : ℕ → Fin k, ∃ b : Fin k, (f ⁻¹' {b}).Infinite

/-- **RT²₂**: every symmetric two-colouring of pairs has an infinite
homogeneous set. -/
def RT2_2 : Prop :=
  ∀ c : PairColoring, ∃ (S : Set ℕ) (b : Bool), IsHomogeneous S c b

/-- A pair colouring is *stable* if for every `i` the colour `c(i, j)`
eventually stabilises as `j → ∞`. -/
def IsStable (c : PairColoring) : Prop :=
  ∀ i, ∃ (N : ℕ) (b : Bool), ∀ j, N ≤ j → c.color i j = b

/-- **SRT²₂**: every stable symmetric two-colouring of pairs has an infinite
homogeneous set. -/
def SRT2_2 : Prop :=
  ∀ c : PairColoring, IsStable c → ∃ (S : Set ℕ) (b : Bool), IsHomogeneous S c b

/-- **COH** (cohesiveness): for every sequence of sets `R n` there is an
infinite set `C` that is, for each `n`, almost contained in `R n` or almost
contained in its complement. -/
def COH : Prop :=
  ∀ R : ℕ → Set ℕ, ∃ C : Set ℕ, C.Infinite ∧
    ∀ n, (∃ N, ∀ m ∈ C, N ≤ m → m ∈ R n) ∨ (∃ N, ∀ m ∈ C, N ≤ m → m ∉ R n)


