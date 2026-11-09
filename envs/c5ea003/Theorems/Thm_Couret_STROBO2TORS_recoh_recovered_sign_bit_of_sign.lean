-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_recovered_sign_bit_of_sign
-- name    : Couret.STROBO2TORS.recoh_recovered_sign_bit_of_sign
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:47.428195+00:00
-- url     : https://prove2.me/theorems/1246ee81-4ea1-4a35-a7e8-25bf885ace90
-- title:
--   An exact nonzero sign reading recovers its bit
-- statement:
--   Let $a\in\mathbb C$ be nonzero and $b\in\mathbb F_2$. Let $\operatorname{bit}(a,o)$ be zero if $o=a$ and one otherwise. Then
--
--   $$\operatorname{bit}(a,(-1)^b a)=b.$$
--
--   The nonzero premise makes the two possible signs distinguishable.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSignRecovery.lean, lines 30–39; source file SHA-256 9c4330cb72ad0993c6c48361a0b68823a89e5af35e3cfb07799a30c9c651fb1c; theorem Couret.STROBO2TORS.recoh_recovered_sign_bit_of_sign

import Aesop
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a
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

theorem recoh_recovered_sign_bit_of_sign (base : ℂ) (hbase : base ≠ 0)
    (bit : ZMod 2) :
    recohRecoveredSignBit base ((if bit = 0 then 1 else -1) * base) = bit := by sorry




variable {G : Type*} [AddCommGroup G] {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2





variable [DecidableEq G]











variable [Fintype G]









end Couret.STROBO2TORS
