-- Prove2me | Definitions.Def_Bridges_EvolvingMathematics_Ecosystem
-- name    : Bridges_EvolvingMathematics_Ecosystem
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:30.769883+00:00
-- url     : https://prove2.me/theorems/a9159ebd-ffc0-4a04-af91-3d227cad1e55
-- title:
--   Aether Catalog definitions — Bridges_EvolvingMathematics_Ecosystem
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.EvolvingMathematics.Ecosystem`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/EvolvingMathematics/Ecosystem.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

# Mathematics as an evolving ecosystem

This file gives a precise, deliberately operational model of the metaphor in the
prompt.  A theory profile records measured connectivity, proof density, and
axiom cost.  The labels `ZFC` and `ZFC + large cardinals` carry no numerical
facts by themselves, so the comparison theorem is first stated with the exact
necessary-and-sufficient empirical criterion and then instantiated on a small
illustrative census.
-/


namespace MathematicalEcosystem

/-- Quantitative data attached to a mathematical theory. -/
structure TheoryProfile where
  connections : ℚ
  proofDensity : ℚ
  axiomCount : ℚ
  connections_nonneg : 0 ≤ connections
  proofDensity_nonneg : 0 ≤ proofDensity
  axiomCount_pos : 0 < axiomCount

/-- Fitness is connectivity times proof density, divided by axiom cost. -/
def fitness (T : TheoryProfile) : ℚ :=
  T.connections * T.proofDensity / T.axiomCount




/-! ## A concrete census

These rational values are an illustrative operationalization, not claims about
absolute proof-theoretic strength.  They can be replaced by any audited census;
the comparison theorem above says exactly what must then be checked.
-/

/-- Illustrative normalized census for ZFC. -/
def zfcProfile : TheoryProfile where
  connections := 10
  proofDensity := 4
  axiomCount := 9
  connections_nonneg := by norm_num
  proofDensity_nonneg := by norm_num
  axiomCount_pos := by norm_num

/-- Illustrative normalized census for ZFC plus large-cardinal principles. -/
def zfcLargeCardinalProfile : TheoryProfile where
  connections := 14
  proofDensity := 6
  axiomCount := 10
  connections_nonneg := by norm_num
  proofDensity_nonneg := by norm_num
  axiomCount_pos := by norm_num



/-! ## Evolution on a finite landscape -/

/-- A global fitness maximum. -/
def IsGlobalMaximum {S : Type*} (F : S → ℚ) (s : S) : Prop :=
  ∀ t, F t ≤ F s

/-- An evolutionary landscape equipped with a natural-valued Lyapunov distance.
The axioms say that every nonstationary update improves fitness and decreases
its distance, and that stationary species are exactly global maxima. -/
structure Landscape (S : Type*) where
  profile : S → TheoryProfile
  evolve : S → S
  distance : S → ℕ
  distance_zero_iff_fixed : ∀ s, distance s = 0 ↔ evolve s = s
  distance_decreases : ∀ s, evolve s ≠ s → distance (evolve s) < distance s
  fitness_increases : ∀ s, evolve s ≠ s → fitness (profile s) < fitness (profile (evolve s))
  maximum_iff_fixed : ∀ s, IsGlobalMaximum (fun t => fitness (profile t)) s ↔ evolve s = s





/-! ## Competitive exclusion

Competitive exclusion is not a consequence of the scalar fitness formula alone:
two distinct profiles can have equal fitness.  The following certified
counterexample makes this obstruction explicit. -/

private def equalFitnessProfileA : TheoryProfile where
  connections := 1
  proofDensity := 2
  axiomCount := 1
  connections_nonneg := by norm_num
  proofDensity_nonneg := by norm_num
  axiomCount_pos := by norm_num

private def equalFitnessProfileB : TheoryProfile where
  connections := 2
  proofDensity := 1
  axiomCount := 1
  connections_nonneg := by norm_num
  proofDensity_nonneg := by norm_num
  axiomCount_pos := by norm_num


/-! Competitive exclusion is therefore modeled as an additional, explicit
resource-allocation rule assigning at most one occupant to each niche. -/

/-- A niche allocation records its (optional) unique occupant. -/
structure NicheAllocation (N S : Type*) where
  occupant : N → Option S

/-- Species `s` occupies niche `n`. -/
def Occupies {N S : Type*} (E : NicheAllocation N S) (s : S) (n : N) : Prop :=
  E.occupant n = some s



end MathematicalEcosystem


