-- Prove2me | Definitions.Def_Shared_Stoneweierstrasslattice_StoneWeierstrassLattice
-- name    : Shared_Stoneweierstrasslattice_StoneWeierstrassLattice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:15:14.223868+00:00
-- url     : https://prove2.me/theorems/83e56f7f-11db-4d24-a533-b40b107e1472
-- title:
--   Aether Catalog definitions — Shared_Stoneweierstrasslattice_StoneWeierstrassLattice
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.Stoneweierstrasslattice.StoneWeierstrassLattice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/Stoneweierstrasslattice/StoneWeierstrassLattice.lean by skeleton subtraction
import Mathlib

/-!
# Lattice closure from linear and absolute-value closure

The elementary identity
`max a b = ((a + b) + |a - b|) / 2` shows that a real linear family of
functions closed under absolute value is a lattice.  This is the algebraic
lattice step used in proofs of the real Stone–Weierstrass theorem.
-/

open Set

namespace StoneWeierstrassLattice

variable {X : Type*}

/-- Closure conditions sufficient for a family of real-valued functions to be a lattice. -/
def IsLinearLattice (A : Set (X → ℝ)) : Prop :=
  (∀ f ∈ A, ∀ g ∈ A, (fun x => f x + g x) ∈ A) ∧
  (∀ f ∈ A, ∀ g ∈ A, (fun x => f x - g x) ∈ A) ∧
  (∀ f ∈ A, (fun x => |f x|) ∈ A) ∧
  (∀ f ∈ A, (fun x => (2 : ℝ)⁻¹ * f x) ∈ A)





end StoneWeierstrassLattice


