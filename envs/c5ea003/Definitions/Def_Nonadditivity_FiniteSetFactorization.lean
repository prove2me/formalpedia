-- Prove2me | Definitions.Def_Nonadditivity_FiniteSetFactorization
-- name    : Nonadditivity_FiniteSetFactorization
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:40:13.888362+00:00
-- url     : https://prove2.me/theorems/d744be47-31cc-4846-98ba-bef2b6faf76f
-- title:
--   Block coefficients for finite-support Gram factorization
-- statement:
--   A finite group-word support determines a difference support and chosen pairs representing its nonidentity words. Selector matrices place coefficient blocks in a larger matrix; positive polar-modulus blocks give the nonconstant Gram assembly and its diagonal correction. The interface defines the scalar and constant corrections, square-root factor coefficients, zero-column padding, and inverse-transpose dilation coefficients used by the finite-support factorization construction. These coefficients are specified independently of a particular finite unitary representation.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/FiniteSetFactorization.lean#L36-L469

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularDilation
import Definitions.Def_Nonadditivity_RegularRestriction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Nonadditivity.MatrixNormReindex
end Nonadditivity.MatrixNormReindex

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/






/-!
# Positive Gram assembly over a finite difference support

Every nonidentity word contributes half a positive modulus block.  Summing
over all such words avoids a choice of inverse-orbit representatives,
including the involution case.  The resulting coefficient matrix is
independent of the unitary representation at which it is evaluated.
The literal dilation coefficients and zero-column padding give the exact
factorization norm identity for every nonempty finite matrix representation.
Its scalar correction is bounded by `|S|` times the original polynomial's
actual infinite left regular norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.FiniteSetFactorization

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

section MatrixBlocks

variable {ζ ι ν : Type*} [Fintype ζ] [DecidableEq ζ]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

/-- Select one coefficient block. -/
def selector (g : ζ) : Matrix ι (ζ × ι) ℂ := fun i p => if p = (g, i) then 1 else 0



/-- Place a matrix in a specified coefficient block. -/
def place (g h : ζ) (A : Matrix ι ι ℂ) : Matrix (ζ × ι) (ζ × ι) ℂ :=
  (selector g).conjTranspose * A * selector h



/-- Insert the full positive polar block at two coefficient rows. -/
def polarInsertion (g h : ζ) (c : Matrix ι ι ℂ) : Matrix (ζ × ι) (ζ × ι) ℂ :=
  let J := Matrix.fromRows (selector g) (selector h)
  J.conjTranspose *
    Matrix.fromBlocks (CFC.abs c.conjTranspose) c c.conjTranspose (CFC.abs c) * J





















end MatrixBlocks

section FiniteSupport

variable {G ι ν : Type*} [Group G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

abbrev Support (S : Finset G) := {g : G // g ∈ S}
abbrev NonidentityWords (S : Finset G) :=
  {w : G // w ∈ (Linearization.differenceSupport S).erase 1}

 theorem exists_pair (S : Finset G) (w : NonidentityWords S) :
    ∃ p : Support S × Support S, p.1.val⁻¹ * p.2.val = w.val := by
  obtain ⟨g, hg, h, hh, heq⟩ :=
    Linearization.mem_differenceSupport.mp (Finset.mem_erase.mp w.property).2
  exact ⟨(⟨g, hg⟩, ⟨h, hh⟩), heq⟩

/-- A genuine representing pair `g,h ∈ S` for each difference word. -/
def representative (S : Finset G) (w : NonidentityWords S) : Support S × Support S :=
  Classical.choose (Nonadditivity.FiniteSetFactorization.exists_pair S w)





/-- All nonidentity words contribute half of the positive polar block. -/
def nonconstantGram (S : Finset G) (c : G → Matrix ι ι ℂ) :
    Matrix (Support S × ι) (Support S × ι) ℂ :=
  ∑ w : NonidentityWords S, (1 / 2 : ℝ) •
    polarInsertion (representative S w).1 (representative S w).2 (c w.val)



/-- The exact constant contribution from the nonidentity moduli. -/
def diagonalCorrection (S : Finset G) (c : G → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ w : NonidentityWords S, CFC.abs (c w.val)

























/-- The additive scalar is chosen from the actual coefficient moduli. -/
def theta (S : Finset G) (c : G → Matrix ι ι ℂ) : ℝ :=
  ‖diagonalCorrection S c + CFC.abs (c 1)‖



def constantCorrection (S : Finset G) (c : G → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  algebraMap ℝ (Matrix ι ι ℂ) (theta S c) + c 1 - diagonalCorrection S c



/-- The positive coefficient matrix with the exact constant correction. -/
def gramMatrix (S : Finset G) (hS : (1 : G) ∈ S) (c : G → Matrix ι ι ℂ) :
    Matrix (Support S × ι) (Support S × ι) ℂ :=
  nonconstantGram S c + place (⟨1, hS⟩ : Support S) ⟨1, hS⟩ (constantCorrection S c)











/-- Genuine square-root coefficients, independent of the representation. -/
def factorCoefficient (S : Finset G) (hS : (1 : G) ∈ S) (c : G → Matrix ι ι ℂ)
    (g : Support S) : Matrix (Support S × ι) ι ℂ :=
  CFC.sqrt (gramMatrix S hS c) * (selector g).conjTranspose









/-- The square coefficient matrices in the manuscript; the identity support
block supplies the zero-column padding of the rectangular factor. -/
def paddedCoefficient (S : Finset G) (hS : (1 : G) ∈ S) (c : G → Matrix ι ι ℂ)
    (g : Support S) : Matrix (Support S × ι) (Support S × ι) ℂ :=
  factorCoefficient S hS c g * selector (⟨1, hS⟩ : Support S)

def paddedPolynomial (S : Finset G) (hS : (1 : G) ∈ S) (c : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    Matrix ((Support S × ι) × ν) ((Support S × ι) × ν) ℂ :=
  ∑ g : Support S, paddedCoefficient S hS c g ⊗ₖ (π g.val : Matrix ν ν ℂ)





end FiniteSupport

section Dilation

variable {G ι ν : Type*} [Group G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]



/-- Actual Hermitian dilation coefficients of an arbitrary polynomial. -/
def dilationCoefficient (a : G → Matrix ι ι ℂ) (w : G) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 0 (a w) (a w⁻¹).conjTranspose 0





















end Dilation

end Nonadditivity.FiniteSetFactorization


