-- Prove2me | Definitions.Def_Applications_EMLQuantumActivation
-- name    : Applications_EMLQuantumActivation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:29.012882+00:00
-- url     : https://prove2.me/theorems/c28384f1-86f5-4219-b554-a2e1070f46af
-- title:
--   Aether Catalog definitions — Applications_EMLQuantumActivation
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.EMLQuantumActivation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/EMLQuantumActivation.lean by skeleton subtraction
import Mathlib

/-!
# Quantum exponential--matrix-logarithm activation

This file tests the proposed quantum EML activation in the general setting of a
unital C⋆-algebra.  It builds on Mathlib's continuous functional calculus and its
existing exponential map from self-adjoint to unitary elements.

The proposed expression is not, in general, unitary: setting the second
Hamiltonian to zero makes the logarithmic factor (and hence the whole neuron)
zero.  Thus it does not define a map into `SU(2)` without an additional
normalisation or a restriction on the second Hamiltonian.  The results below
formalize this obstruction; they apply in particular to the C⋆-algebra of
operators on a two-dimensional complex Hilbert space.
-/

noncomputable section

open Complex NormedSpace

namespace QuantumEML

variable {A : Type*} [CStarAlgebra A]

/-- The quantum EML expression proposed in the mission: the unitary exponential
of a self-adjoint first Hamiltonian, multiplied by the principal matrix
logarithm (continuous functional calculus) of `1 + i H₂`. -/
def neuron (H₁ H₂ : selfAdjoint A) : A :=
  (selfAdjoint.expUnitary H₁ : A) * cfc Complex.log (1 + I • (H₂ : A))






end QuantumEML


