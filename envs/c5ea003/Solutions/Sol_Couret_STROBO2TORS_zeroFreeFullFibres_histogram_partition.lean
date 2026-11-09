-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_histogram_partition
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:30:37.453207+00:00
-- url     : https://prove2.me/submissions/a1c2347c-2f81-43b4-830f-287181c76e33

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFree_ordinary_exceptional_disjoint
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]























/-- Exact disjoint aggregation of the histogram of all nonempty zero-free
square fibres. Distinct origin types contribute ADDITIVELY even if their
fibre cardinalities coincide (notably when |G[2]|=2). -/
theorem p2m_local_zeroFreeFullFibres_histogram_partition (k : ℕ) :
    ((zeroFreeFullFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = k)).card =
    ((zeroFreeOrdinaryFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = k)).card +
    ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = k)).card := by
  rw [zeroFreeFullFibres_eq_union, Finset.filter_union]
  have hd : Disjoint
      ((zeroFreeOrdinaryFibres : Finset (Finset (Finset G))).filter (fun R => R.card = k))
      ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter (fun R => R.card = k)) := by
    apply Finset.disjoint_left.mpr
    intro R hO hE
    exact (Finset.disjoint_left.mp (zeroFree_ordinary_exceptional_disjoint (G := G)))
      (Finset.mem_filter.mp hO).1 (Finset.mem_filter.mp hE).1
  exact Finset.card_union_of_disjoint hd













/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (k : Nat),
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (fun R => @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R) k)
        (fun a => instDecidableEqNat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) a) k)
        (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (fun R => @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R) k)
          (fun a => instDecidableEqNat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) a) k)
          (@Couret.STROBO2TORS.zeroFreeOrdinaryFibres.{p2m_u_0} G inst inst_1 inst_2)))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (fun R => @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R) k)
          (fun a => instDecidableEqNat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) a) k)
          (@Couret.STROBO2TORS.zeroFreeExceptionalFibres.{p2m_u_0} G inst inst_1 inst_2)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_histogram_partition

