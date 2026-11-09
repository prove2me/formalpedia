-- Prove2me | Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a
-- name    : Couret_RecohSignRecovery_71a8a4a1ce8a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:36.209287+00:00
-- url     : https://prove2.me/theorems/bf51f53c-9392-4c8e-a01d-657326b7d9b1
-- title:
--   Recovery of two-torsion translations from signs
-- statement:
--   Defines the recovered binary bit to be zero when an observed complex value equals its base value and one otherwise. Given an additive coordinate equivalence between the two-torsion subgroup and $r$ binary coordinates, applies its inverse to all recovered bits. Correctness needs later hypotheses ensuring the readings are compatible signs and the base readings are nonzero.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSignRecovery.lean; source file SHA-256 9c4330cb72ad0993c6c48361a0b68823a89e5af35e3cfb07799a30c9c651fb1c

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
Direct recovery of the unknown two-torsion translation from the signs of
nonzero character readings.  The recovered coordinates are explicit: a
coordinate is zero when the observed and base readings agree, and one
otherwise.  Accepted readings must equal the base reading or its negative.

This module proves both completeness for actual translated observations and
soundness for accepted signs.  It also constructs compatible coordinates for
a separating bank of the minimum size, and instantiates such a bank with the
already proved two-primary character construction.  Three-primary readings
are proved invariant under every recovered two-torsion translation.

Equality of complex values and the inverse coordinate map are noncomputable
here.  No executable arithmetic on cyclotomic representations, running-time
bound, or extraction of a Python implementation is claimed by this module.
-/

namespace Couret.STROBO2TORS

/-- One explicit coordinate recovered by comparing two complex readings. -/
noncomputable def recohRecoveredSignBit (base obs : ℂ) : ZMod 2 := by
  classical
  exact if obs = base then 0 else 1





variable {G : Type*} [AddCommGroup G] {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2

/-- Recover a two-torsion element from the explicit vector of comparison
bits, through a specified additive coordinate equivalence. -/
noncomputable def recohRecoverTranslation
    (e : H₂ ≃+ (Fin r → ZMod 2)) (base obs : Fin r → ℂ) : H₂ :=
  e.symm (fun i => recohRecoveredSignBit (base i) (obs i))



variable [DecidableEq G]











variable [Fintype G]









end Couret.STROBO2TORS


