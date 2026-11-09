-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeCollisionDarts_delta_partition
-- name    : Couret.STROBO2TORS.zeroFreeCollisionDarts_delta_partition
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:47.395233+00:00
-- url     : https://prove2.me/theorems/e2449702-7058-4a32-87b0-1b4a98175a53
-- title:
--   Collision darts split into distances two four and six
-- statement:
--   Let $G$ be a finite abelian group and let $\mathcal Z$ be the distinct nonempty zero-free parts of triple square fibres. A support is zero-free when it does not contain zero. Let $D$ be ordered pairs $(S,T)$ of distinct zero-free triples with equal ordered-square counts; let $D_k$ further require $|S\triangle T|=k$. Let $c_k$ count the corresponding unordered pairs. Then
--
--   $$|D|=|D_2|+|D_4|+|D_6|.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/46d8415e210e3292a6e74b2bd990cd104cfa2835/research/strobo-2tors-2026-10-12/lean/Strobo2TorsFibreMoment.lean#L184-L245, lines 184–245; source file SHA-256 d086c5e93fc7de275469fcb96fb6cdd5cd945016a356726bacaff4d0ce5390dc; theorem Couret.STROBO2TORS.zeroFreeCollisionDarts_delta_partition

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
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_cases
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

theorem zeroFreeCollisionDarts_delta_partition :
    (zeroFreeCollisionDarts (G := G)).card =
      ((zeroFreeCollisionDarts (G := G)).filter
        (fun p => (p.1 ∆ p.2).card = 2)).card +
      ((zeroFreeCollisionDarts (G := G)).filter
        (fun p => (p.1 ∆ p.2).card = 4)).card +
      ((zeroFreeCollisionDarts (G := G)).filter
        (fun p => (p.1 ∆ p.2).card = 6)).card := by sorry










end Couret.STROBO2TORS
