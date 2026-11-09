-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeCollisionDarts_eq_fibre_biUnion
-- name    : Couret.STROBO2TORS.zeroFreeCollisionDarts_eq_fibre_biUnion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:30.421201+00:00
-- url     : https://prove2.me/theorems/e2ccc969-e028-46a1-acb1-6709a011b0a6
-- title:
--   Collision darts decompose into fibre off-diagonals
-- statement:
--   Let $G$ be a finite abelian group and let $\mathcal Z$ be the distinct nonempty zero-free parts of triple square fibres. A support is zero-free when it does not contain zero. Let $D$ be ordered pairs $(S,T)$ of distinct zero-free triples with equal ordered-square counts; let $D_k$ further require $|S\triangle T|=k$. Let $c_k$ count the corresponding unordered pairs. Then
--
--   $$D=\bigcup_{F\in\mathcal Z}\{(S,T)\in F^2:S\ne T\}.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/46d8415e210e3292a6e74b2bd990cd104cfa2835/research/strobo-2tors-2026-10-12/lean/Strobo2TorsFibreMoment.lean#L99-L117, lines 99–117; source file SHA-256 d086c5e93fc7de275469fcb96fb6cdd5cd945016a356726bacaff4d0ce5390dc; theorem Couret.STROBO2TORS.zeroFreeCollisionDarts_eq_fibre_biUnion

import Aesop
import Definitions.Def_Couret_Strobo2TorsFibreMoment_8377f9a18ab8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_squareFibre_member
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Mathlib.Data.Sym.Card

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
M002.4: a combinatorial, rather than numerical, bridge between the second
binomial moment of the nonempty zero-free square fibres and the three
symmetric-difference collision edge counts.

The common object is an ordered pair of distinct supports in a single
restricted fibre. Each undirected graph edge has exactly two orientations.
No translation orbit is divided out, and no division of any numerical
closed-form count is used.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem zeroFreeCollisionDarts_eq_fibre_biUnion :
    (zeroFreeCollisionDarts (G := G)) =
      (zeroFreeFullFibres : Finset (Finset (Finset G))).biUnion
        (fun F => F.offDiag) := by sorry




















end Couret.STROBO2TORS
