-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeCollisionDarts_card_eq_twice_moment
-- name    : Couret.STROBO2TORS.zeroFreeCollisionDarts_card_eq_twice_moment
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:36.181187+00:00
-- url     : https://prove2.me/theorems/203b7eb0-9cc0-42d2-a8db-25b42d1cc0b3
-- title:
--   Collision darts count twice the fibre binomial moment
-- statement:
--   Let $G$ be a finite abelian group and let $\mathcal Z$ be the distinct nonempty zero-free parts of triple square fibres. A support is zero-free when it does not contain zero. Let $D$ be ordered pairs $(S,T)$ of distinct zero-free triples with equal ordered-square counts; let $D_k$ further require $|S\triangle T|=k$. Let $c_k$ count the corresponding unordered pairs. Then
--
--   $$|D|=2\sum_{F\in\mathcal Z}\binom{|F|}{2}.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/46d8415e210e3292a6e74b2bd990cd104cfa2835/research/strobo-2tors-2026-10-12/lean/Strobo2TorsFibreMoment.lean#L144-L166, lines 144–166; source file SHA-256 d086c5e93fc7de275469fcb96fb6cdd5cd945016a356726bacaff4d0ce5390dc; theorem Couret.STROBO2TORS.zeroFreeCollisionDarts_card_eq_twice_moment

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
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeCollisionDarts_eq_fibre_biUnion
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

theorem zeroFreeCollisionDarts_card_eq_twice_moment :
    (zeroFreeCollisionDarts (G := G)).card =
      2 * ∑ F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))),
        F.card.choose 2 := by sorry














end Couret.STROBO2TORS
