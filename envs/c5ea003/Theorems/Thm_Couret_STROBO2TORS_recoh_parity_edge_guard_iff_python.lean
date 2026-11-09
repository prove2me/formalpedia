-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_parity_edge_guard_iff_python
-- name    : Couret.STROBO2TORS.recoh_parity_edge_guard_iff_python
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:55:56.786314+00:00
-- url     : https://prove2.me/theorems/de03d0e5-c238-4113-920d-c821298075ac
-- title:
--   The parity edge guard equals the residual arithmetic check
-- statement:
--   Let $G$ be an abelian group. Let $U$ be any finite support and $R:G\to\mathbb N$. Write $i_z=[R(z)\text{ odd}]$ on $U$ and let $E=\{z\in U:(R(z)-i_z)/2>0\}$. Then the guard $R(z)=i_z+2[z\in E]$ for every $z\in U$ is equivalent to
--
--   $$\forall z\in U:\quad i_z\le R(z),\quad R(z)-i_z\equiv0\pmod2,\quad(R(z)-i_z)/2\le1.$$
--
--   This identifies the finite-set parity guard with the Python residual test, using natural subtraction and division.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityGuardBridge.lean, lines 32–55; source file SHA-256 06162ab7b538e9783989f43f6e8c4037a3c37096e45d688909d264f70b074b5d; theorem Couret.STROBO2TORS.recoh_parity_edge_guard_iff_python

import Aesop
import Definitions.Def_Couret_RecohParityGuardBridge_a0468e3b1d7b
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





variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [AddCommGroup G] in
theorem recoh_parity_edge_guard_iff_python (U : Finset G) (R : G → ℕ) :
    recohParityEdgeGuard U R ↔
      ∀ z ∈ U, recohPythonResidualGuard (R z)
        (recohParityIndicator (recohParityOddSupport U R) z) := by sorry




end Couret.STROBO2TORS
