-- Prove2me | Definitions.Def_Probability_WignerRademacherEnsemble
-- name    : Probability_WignerRademacherEnsemble
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:24.808654+00:00
-- url     : https://prove2.me/theorems/4532a604-2585-450b-a4e5-021b8333b873
-- title:
--   Aether Catalog definitions — Probability_WignerRademacherEnsemble
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerRademacherEnsemble`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerRademacherEnsemble.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The symmetric Rademacher Wigner ensemble and its spectral moments

This file constructs a concrete Wigner ensemble — the uniform measure on real
symmetric `N × N` sign matrices with zero diagonal — and computes the first
nontrivial normalised spectral moments of `W/√N` by the moment method:

* the second moment is **deterministically** `1 - 1/N` (self-averaging), and
* the expected fourth moment is exactly `(N-1)(2N-3)/N²`.

Both converge to the corresponding moments of the Wigner semicircle law,
`C₁ = 1` and `C₂ = 2` (see `Probability.WignerSemicircleMoments`), which is the
moment-method statement of the semicircle law at orders 2 and 4.

The key probabilistic input is a *sign-flip involution*: if some edge of the
closed walk `i → j → k → l → i` is traversed an odd number of times, flipping
the corresponding Rademacher variable negates the summand, so the expectation
vanishes.  This replaces the usual independence/factorisation argument by an
exact combinatorial symmetry.
-/

open Matrix BigOperators Finset

namespace RademacherWigner

variable {N : ℕ}

/-- A configuration of the ensemble: a sign for every ordered pair of indices
(only the pairs `i < j` are ever read). -/
abbrev Config (N : ℕ) := (Fin N × Fin N) → Bool

/-- The Rademacher sign attached to a Boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1



/-- The unordered edge `{i, j}`, represented by the increasing ordered pair. -/
def edgeOf (i j : Fin N) : Fin N × Fin N := if i < j then (i, j) else (j, i)



/-- The `(i, j)` entry of the sign matrix: zero on the diagonal, a Rademacher
sign off it, symmetric by construction. -/
def entry (g : Config N) (i j : Fin N) : ℝ :=
  if i = j then 0 else sgn (g (edgeOf i j))




/-- The random symmetric sign matrix. -/
def W (g : Config N) : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => entry g i j



/-! ### The second spectral moment is deterministic -/


/-! ### Expectation over the ensemble -/

/-- The uniform expectation over all sign configurations. -/
noncomputable def expect (f : Config N → ℝ) : ℝ :=
  (∑ g : Config N, f g) / (Fintype.card (Config N) : ℝ)





/-! ### The sign-flip involution -/

/-- Flipping the Rademacher sign attached to one edge is an involution of the
configuration space. -/
def flipEdge (p : Fin N × Fin N) : Config N ≃ Config N where
  toFun g := Function.update g p (!(g p))
  invFun g := Function.update g p (!(g p))
  left_inv g := by
    funext q
    by_cases h : q = p <;> simp [Function.update, h]
  right_inv g := by
    funext q
    by_cases h : q = p <;> simp [Function.update, h]


/-! ### The fourth moment -/







/-- The indicator of a "paired" closed 4-walk. -/
def pairedWalk (i j k l : Fin N) : ℝ :=
  if i ≠ j ∧ j ≠ k ∧ k ≠ l ∧ l ≠ i ∧ (i = k ∨ j = l) then 1 else 0


/-- Indicator of the walks with `k = i` (the two edges `{i,j}`, `{i,l}` doubled). -/
def indA (i j k l : Fin N) : ℝ :=
  (if j = i then 0 else 1) * (if k = i then 1 else 0) * (if l = i then 0 else 1)

/-- Indicator of the walks with `l = j`. -/
def indB (i j k l : Fin N) : ℝ :=
  (if i = j then 0 else 1) * (if k = j then 0 else 1) * (if l = j then 1 else 0)

/-- Indicator of the doubly-degenerate walks `k = i` and `l = j`. -/
def indC (i j k l : Fin N) : ℝ :=
  (if i = j then 0 else 1) * (if k = i then 1 else 0) * (if l = j then 1 else 0)










end RademacherWigner


