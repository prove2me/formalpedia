-- Prove2me | Definitions.Def_Couret_RecohParityGuardBridge_a0468e3b1d7b
-- name    : Couret_RecohParityGuardBridge_a0468e3b1d7b
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:12:13.390769+00:00
-- url     : https://prove2.me/theorems/0d0b9b84-e2b0-4573-bdc8-c09b2a46f173
-- title:
--   The residual arithmetic guard
-- statement:
--   For natural $n,i$, the Python residual condition is $$i\le n,\qquad(n-i)\bmod2=0,\qquad(n-i)/2\le1.$$ The explicit lower bound prevents truncated subtraction from accepting a negative residual. This predicate provides the arithmetic interface for the singleton parity guard.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityGuardBridge.lean; source file SHA-256 06162ab7b538e9783989f43f6e8c4037a3c37096e45d688909d264f70b074b5d

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohParityGenerator_deb90a4bb68d

set_option autoImplicit false

/-!
Exact arithmetic correspondence between the Lean residual guards and the
subtraction, parity and indicator-value guards in Python v0.2.

This proves equal mathematical predicates. It is not a formal semantics of
Python integer operations, parsing, exceptions or serialization.
-/

namespace Couret.STROBO2TORS

/-- A residual is obtained by nonnegative exact division by two, and each
positive retained coefficient is one. Zero residuals are omitted. -/
def recohPythonResidualGuard (n i : ℕ) : Prop :=
  i ≤ n ∧ (n - i) % 2 = 0 ∧ (n - i) / 2 ≤ 1



variable {G : Type*} [AddCommGroup G] [DecidableEq G]





end Couret.STROBO2TORS


