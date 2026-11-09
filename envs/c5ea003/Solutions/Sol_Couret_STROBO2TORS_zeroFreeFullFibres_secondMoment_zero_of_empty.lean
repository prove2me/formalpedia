-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_secondMoment_zero_of_empty
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:58:16.213733+00:00
-- url     : https://prove2.me/submissions/ec346ef5-f650-40cb-952d-50ccd1499dae

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



























/-- Explicitly includes an empty collection of surviving fibres. -/
theorem p2m_local_zeroFreeFullFibres_secondMoment_zero_of_empty
    (h : (zeroFreeFullFibres : Finset (Finset (Finset G))) = ∅) :
    (∑ F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))),
      F.card.choose 2) = 0 := by
  simp [h]

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2)
      (@EmptyCollection.emptyCollection.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (@Finset.instEmptyCollection.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))) →
    @Eq.{1} Nat
      (@Finset.sum.{p2m_u_0, 0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) Nat Nat.instAddCommMonoid
        (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) fun F =>
        Nat.choose (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) F)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_secondMoment_zero_of_empty

