-- Prove2me | Definitions.Def_Tropical_AperiodicMonotile_HierarchicalSpectrum
-- name    : Tropical_AperiodicMonotile_HierarchicalSpectrum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:18.036731+00:00
-- url     : https://prove2.me/theorems/6c4431b0-69ad-4d27-9980-b88783be266c
-- title:
--   Aether Catalog definitions — Tropical_AperiodicMonotile_HierarchicalSpectrum
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.AperiodicMonotile.HierarchicalSpectrum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/AperiodicMonotile/HierarchicalSpectrum.lean by skeleton subtraction
import Mathlib

/-!
# A rigorous abstract core for a hierarchical monotile spectrum

This file does **not** claim to formalize the geometry of the 2023 hat or turtle.
Instead it isolates and proves the algebraic implication needed by any such
formalization: if every tiling locally decodes a hierarchy of residue addresses
at arbitrarily large substitution scales, then the tiling has no nonzero
translation period.  It also gives a simple continuous, injective affine
parameter path with distinguished endpoints, suitable as an abstract parameter
space for a proposed spectrum.
-/

namespace AperiodicMonotile

/-- Translation by `p` is a period of a one-dimensional configuration. -/
def IsPeriod {α : Type*} (c : ℤ → α) (p : ℤ) : Prop :=
  ∀ x, c (x + p) = c x

/-- `coarse` is locally decoded from `fine`. -/
def FactorsThrough {α β : Type*} (fine : ℤ → α) (coarse : ℤ → β) : Prop :=
  ∃ decode : α → β, coarse = decode ∘ fine

/-
Periods descend through a local decoding.
-/

/-- The level-`n` address records position modulo the substitution scale `2^n`. -/
def levelAddress (n : ℕ) (x : ℤ) : ZMod (2 ^ n) := x

/-
A period of a level address is divisible by that level's scale.
-/

/-
No nonzero integer is divisible by every power of two.
-/

/-- The full hierarchy consists of addresses at every substitution level. -/
def addressHierarchy (x : ℤ) (n : ℕ) : ZMod (2 ^ n) := levelAddress n x

/-
The full address hierarchy has only the zero translation period.
-/

/-- A configuration enforces the hierarchy when every level is locally decodable. -/
def EnforcesHierarchy {α : Type*} (c : ℤ → α) : Prop :=
  ∀ n : ℕ, FactorsThrough c (levelAddress n)

/-
Hierarchy enforcement rules out every nonzero translation period.
-/

/-- An abstract two-coordinate affine interpolation between two endpoint shapes. -/
def spectrumPath (t : ℝ) : ℝ × ℝ := (1 - t, t)

/-
The interpolation has the intended `hat` endpoint.
-/

/-
The interpolation has the intended `turtle` endpoint.
-/

/-
Distinct parameters give distinct points on the affine spectrum path.
-/

/-
The abstract spectrum path is continuous.
-/

/--
A candidate spectrum system supplies configurations at every parameter and a
proof that its substitution rule decodes every binary hierarchy level.
-/
structure SpectrumSystem where
  TileState : Type*
  configuration : ℝ → ℤ → TileState
  enforces : ∀ t ∈ Set.Icc (0 : ℝ) 1, EnforcesHierarchy (configuration t)

/-
A concrete witness that hierarchy enforcement is consistent: each tile state
stores the complete compatible list of level addresses.
-/

/-
Every member of a hierarchy-enforcing candidate spectrum is aperiodic.
-/

/-
No two members of such a spectrum can share a common nonzero period.  This is
stronger than merely saying that each individual member is aperiodic.
-/

end AperiodicMonotile


