-- Prove2me | Definitions.Def_NumberTheory_NormalityConverse
-- name    : NumberTheory_NormalityConverse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:44.724693+00:00
-- url     : https://prove2.me/theorems/f396e247-03c6-4d78-841f-a73ce18d4352
-- title:
--   Aether Catalog definitions — NumberTheory_NormalityConverse
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.NormalityConverse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/NormalityConverse.lean by skeleton subtraction
import Mathlib

/-!
# Aligned-cylinder frequencies and interval equidistribution

This file formalizes the approximation step in the converse normality criterion.
An arbitrary interval is squeezed between aligned base-`b` intervals whose lengths
approach its length.  Convergence of the two aligned-interval frequencies then
forces convergence of the arbitrary interval frequency.
-/

namespace NormalityConverse

open Filter Set
open scoped Topology

/-- The empirical frequency of a predicate among the first `N` indices. -/
noncomputable def empiricalFrequency (P : ℕ → Prop) [DecidablePred P] (N : ℕ) : ℝ :=
  ((Finset.filter P (Finset.range N)).card : ℝ) / N

/-- Interval equidistribution in the unit interval. -/
def IntervalEquidistributed (u : ℕ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 →
    Tendsto (empiricalFrequency (fun n => u n ∈ Ico a c)) atTop (𝓝 (c - a))

/-- An arbitrary interval admits arbitrarily accurate inner and outer aligned
base-`b` approximations, and the empirical frequencies of those aligned intervals
have the expected limits. -/
def HasBAdicSandwichFrequencies (b : ℕ) (u : ℕ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∃ k Ai Ci Ao Co : ℕ,
      Ai < Ci ∧ Ci ≤ b ^ k ∧ Ao < Co ∧ Co ≤ b ^ k ∧
      Ico ((Ai : ℝ) / (b : ℝ) ^ k) ((Ci : ℝ) / (b : ℝ) ^ k) ⊆ Ico a c ∧
      Ico a c ⊆ Ico ((Ao : ℝ) / (b : ℝ) ^ k) ((Co : ℝ) / (b : ℝ) ^ k) ∧
      c - a - ε < ((Ci : ℝ) - Ai) / (b : ℝ) ^ k ∧
      ((Co : ℝ) - Ao) / (b : ℝ) ^ k < c - a + ε ∧
      Tendsto
        (empiricalFrequency (fun n => u n ∈
          Ico ((Ai : ℝ) / (b : ℝ) ^ k) ((Ci : ℝ) / (b : ℝ) ^ k)))
        atTop (𝓝 (((Ci : ℝ) - Ai) / (b : ℝ) ^ k)) ∧
      Tendsto
        (empiricalFrequency (fun n => u n ∈
          Ico ((Ao : ℝ) / (b : ℝ) ^ k) ((Co : ℝ) / (b : ℝ) ^ k)))
        atTop (𝓝 (((Co : ℝ) - Ao) / (b : ℝ) ^ k))

/-- Uniform limiting frequencies for every interval whose endpoints lie on one
base-`b` grid.  This is the aligned-cylinder hypothesis used by the converse. -/
def HasBAdicIntervalFrequencies (b : ℕ) (u : ℕ → ℝ) : Prop :=
  2 ≤ b ∧ ∀ k A C : ℕ, A < C → C ≤ b ^ k →
    Tendsto
      (empiricalFrequency (fun n => u n ∈
        Ico ((A : ℝ) / (b : ℝ) ^ k) ((C : ℝ) / (b : ℝ) ^ k)))
      atTop (𝓝 (((C : ℝ) - A) / (b : ℝ) ^ k))

/-- Uniform limiting frequencies for the individual aligned base-`b` cylinder
cells.  This is the usual digit-word hypothesis: at depth `k`, each of the
`b^k` cells has limiting frequency `b⁻ᵏ`. -/
def HasBAdicCylinderFrequencies (b : ℕ) (u : ℕ → ℝ) : Prop :=
  2 ≤ b ∧ ∀ k A : ℕ, A < b ^ k →
    Tendsto
      (empiricalFrequency (fun n => u n ∈
        Ico ((A : ℝ) / (b : ℝ) ^ k) (((A : ℝ) + 1) / (b : ℝ) ^ k)))
      atTop (𝓝 (1 / (b : ℝ) ^ k))












end NormalityConverse


