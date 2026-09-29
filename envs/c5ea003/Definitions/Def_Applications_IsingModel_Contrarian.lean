-- Prove2me | Definitions.Def_Applications_IsingModel_Contrarian
-- name    : Applications_IsingModel_Contrarian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:04.540099+00:00
-- url     : https://prove2.me/theorems/594e4259-4dca-4e9b-a8ac-d5129a29eefe
-- title:
--   Aether Catalog definitions — Applications_IsingModel_Contrarian
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.IsingModel.Contrarian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/IsingModel/Contrarian.lean by skeleton subtraction
import Mathlib

/-!
# Contrarian results for finite-volume Ising symmetry

A frequently stated but false finite-volume version of spontaneous symmetry
breaking says that a zero-field Gibbs state can already have nonzero expected
magnetization.  The theorem below proves the opposite in a model-independent
finite setting: any finite Gibbs ensemble with a fixed-point-free or non-fixed-
point-free involutive spin flip, flip-invariant energy, and odd magnetization has
exactly zero expected magnetization.

This does not contradict the infinite-volume Ising transition.  Spontaneous
magnetization requires first selecting plus boundary conditions (or a positive
field) and then taking a thermodynamic limit; the symmetric finite-volume state
is always the equal mixture of its two flipped phases.
-/

noncomputable section

namespace Ising.Contrarian

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- Finite-volume zero-field partition function. -/
def partition (β : ℝ) (energy : Ω → ℝ) : ℝ :=
  ∑ ω, Real.exp (-β * energy ω)

/-- Unnormalised first moment of an observable. -/
def numerator (β : ℝ) (energy observable : Ω → ℝ) : ℝ :=
  ∑ ω, Real.exp (-β * energy ω) * observable ω

/-- Finite-volume Gibbs expectation. -/
def gibbsExpectation (β : ℝ) (energy observable : Ω → ℝ) : ℝ :=
  numerator β energy observable / partition β energy






end Ising.Contrarian


