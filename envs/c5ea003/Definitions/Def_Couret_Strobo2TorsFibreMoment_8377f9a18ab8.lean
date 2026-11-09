-- Prove2me | Definitions.Def_Couret_Strobo2TorsFibreMoment_8377f9a18ab8
-- name    : Couret_Strobo2TorsFibreMoment_8377f9a18ab8
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:04:20.788194+00:00
-- url     : https://prove2.me/theorems/dd71738b-b449-4728-a035-f01c75d99452
-- title:
--   Ordered zero-free collision pairs
-- statement:
--   For a finite additive commutative group with decidable equality, zeroFreeCollisionDarts is the finite set of ordered pairs (S,T) of distinct three-element supports, both avoiding zero, whose labelled ordered additive convolution-square coefficients agree at every group element. The definition retains both orientations and uses supports themselves, without quotienting by translations. It supplies no numerical moment identity on its own.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/46d8415e210e3292a6e74b2bd990cd104cfa2835/research/strobo-2tors-2026-10-12/lean/Strobo2TorsFibreMoment.lean; source file SHA-256 d086c5e93fc7de275469fcb96fb6cdd5cd945016a356726bacaff4d0ce5390dc

import Aesop
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

/-- Ordered pairs of distinct zero-free three-element supports with exactly
the same labelled ordered convolution square. -/
noncomputable def zeroFreeCollisionDarts : Finset (Finset G × Finset G) :=
  (Finset.univ : Finset (Finset G × Finset G)).filter
    (fun p => p.1.card = 3 ∧ p.2.card = 3 ∧ p.1 ≠ p.2 ∧
      (∀ z : G, orderedSquare p.1 z = orderedSquare p.2 z) ∧
      0 ∉ p.1 ∧ 0 ∉ p.2)



























end Couret.STROBO2TORS


