-- Prove2me | Definitions.Def_Logic_Rademacher_Basic
-- name    : Logic_Rademacher_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:12.209353+00:00
-- url     : https://prove2.me/theorems/3952c46b-2323-49ad-98f2-604fe1532c65
-- title:
--   Aether Catalog definitions — Logic_Rademacher_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Rademacher.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Rademacher/Basic.lean by skeleton subtraction
import Mathlib
/-
# Empirical Rademacher complexity: definitions and basic calculus

This file sets up the *empirical Rademacher complexity* of a class of real vectors
indexed by a finite sample of size `n`.  If `F : Set (Fin n → ℝ)` is the restriction
of a hypothesis class to a sample `x₁, …, xₙ`, its empirical Rademacher complexity is

  `R(F) = 𝔼_σ [ sup_{v ∈ F} (1/n) ∑ i, σ i * v i ]`,

where `σ` ranges uniformly over the `2ⁿ` sign vectors in `{-1, 1}ⁿ`.
The expectation is realised as an explicit finite average over `Fin n → Bool`.

The basic calculus proved here: the complexity of a singleton vanishes, it is
monotone in the class, nonnegative for nonempty classes, homogeneous under scaling,
invariant under translation, and bounded by any uniform bound on the coordinates.
-/

namespace Rademacher

open Finset

variable {n : ℕ}

/-- The sign vector attached to a boolean vector: `true ↦ 1`, `false ↦ -1`. -/
def sgn (ε : Fin n → Bool) (i : Fin n) : ℝ := if ε i then 1 else -1




/-- The linear functional `v ↦ (1/n) ∑ σ i * v i` associated with a sign vector. -/
noncomputable def signAvg (ε : Fin n → Bool) (v : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, sgn ε i * v i

/-- The empirical Rademacher complexity of a class `F` of vectors:
the average over all `2ⁿ` sign patterns of the supremum of `signAvg`. -/
noncomputable def rad (F : Set (Fin n → ℝ)) : ℝ :=
  (∑ ε : Fin n → Bool, sSup (signAvg ε '' F)) / 2 ^ n













end Rademacher


