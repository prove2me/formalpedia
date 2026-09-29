-- Prove2me | Definitions.Def_Applications_LFunctionUniverse_PeriodicUniverse
-- name    : Applications_LFunctionUniverse_PeriodicUniverse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:09.284548+00:00
-- url     : https://prove2.me/theorems/4608ebe6-c7c4-4415-acd4-84987f0f57f4
-- title:
--   Aether Catalog definitions — Applications_LFunctionUniverse_PeriodicUniverse
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.LFunctionUniverse.PeriodicUniverse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/LFunctionUniverse/PeriodicUniverse.lean by skeleton subtraction
import Mathlib

/-!
# The L-function universe, part II: the periodic/arithmetic universe is countable

The Dirichlet L-functions — the L-functions attached to Dirichlet characters — have
coefficient sequences `a(k) = χ(k)` that are **periodic** (period dividing the
conductor) and take values in a **countable** set (roots of unity, together with
`0`).  This is the arithmetic constraint that tames the otherwise uncountable
universe of Dirichlet series studied in `NaiveUniverse.lean`.

The main abstract result of this file is:

* `periodicSeq_countable`: for any *countable* value type `V`, the set of periodic
  sequences `ℕ → V` is countable.

The intuition ("a periodic sequence is determined by a finite block of data") is
made precise via the surjection sending the finite data `(period, one full block of
values)` to the corresponding periodic sequence.

We then apply the countable-value idea to the genuine number-theoretic object: the
family of all Dirichlet characters (over all moduli) is countable, so there are only
countably many Dirichlet L-functions.
-/

open scoped Classical

namespace LFunctionUniverse

/-- A sequence `a : ℕ → V` is *periodic* if it has some strictly positive period. -/
def IsPeriodicSeq {V : Type*} (a : ℕ → V) : Prop :=
  ∃ n : ℕ, 0 < n ∧ Function.Periodic a n




/-- The coefficient sequence `k ↦ χ(k)` of a Dirichlet character `χ` modulo `n`. -/
noncomputable def charCoeff {n : ℕ} (χ : DirichletCharacter ℂ n) : ℕ → ℂ :=
  fun k => χ (k : ZMod n)





end LFunctionUniverse


