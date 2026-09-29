-- Prove2me | Definitions.Def_Speculative_RudyRucker_ComputationalUniverse
-- name    : Speculative_RudyRucker_ComputationalUniverse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:47.875438+00:00
-- url     : https://prove2.me/theorems/b2132c0e-44d7-4136-9fc1-f991c80de761
-- title:
--   Aether Catalog definitions — Speculative_RudyRucker_ComputationalUniverse
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.RudyRucker.ComputationalUniverse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/RudyRucker/ComputationalUniverse.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.RudyRucker.ComputationalUniverse

Auto-generated from theorem catalog database.
Domain: Speculative/RudyRucker
Declarations: 11
-/

/-- A 1D binary cellular automaton configuration is a function from ℤ to Bool. -/
def CAConfig := ℤ → Bool

/-- A neighborhood rule for a 1D CA with radius 1 looks at 3 cells. -/
def CArule := Bool → Bool → Bool → Bool

/-- Apply a CA rule to evolve one step. -/
def evolve (rule : CArule) (config : CAConfig) : CAConfig :=
  fun i => rule (config (i - 1)) (config i) (config (i + 1))


/-- Iterated evolution of a CA for n steps. -/
def evolve_n (rule : CArule) (config : CAConfig) : ℕ → CAConfig
  | 0 => config
  | n + 1 => evolve rule (evolve_n rule config n)


/-- Shift a configuration by k positions. -/
def shift (config : CAConfig) (k : ℤ) : CAConfig :=
  fun i => config (i + k)


/-- A Garden of Eden configuration has no predecessor under the given rule. -/
def is_garden_of_eden (rule : CArule) (config : CAConfig) : Prop :=
  ¬ ∃ prev : CAConfig, evolve rule prev = config

/-- A CA rule is reversible if its evolution function is bijective. -/
def is_reversible (rule : CArule) : Prop :=
  Function.Bijective (evolve rule)


