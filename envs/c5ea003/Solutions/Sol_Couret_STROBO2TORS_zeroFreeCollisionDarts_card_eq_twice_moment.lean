-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeCollisionDarts_card_eq_twice_moment
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:39.733786+00:00
-- url     : https://prove2.me/submissions/e0196446-364a-48ff-abc2-6bbddc2bec8f

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





/-- A support in a surviving restricted fibre uniquely determines the
whole restricted fibre, even in small groups. -/
private theorem zeroFreeFibre_eq_of_mem
    (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))))
    (S : Finset G) (hSF : S ∈ F) :
    S.card = 3 ∧ 0 ∉ S ∧ F = withoutZero (squareFibre S) := by
  change F ∈ (nonemptyFullFibres (G := G)).image (withoutZero (G := G)) at hF
  obtain ⟨K, hK, hKF⟩ := Finset.mem_image.mp hF
  obtain ⟨hKall, _⟩ := Finset.mem_filter.mp hK
  have hSrest : S ∈ withoutZero K := by
    rw [hKF]
    exact hSF
  have hSK : S ∈ K := (Finset.mem_filter.mp hSrest).1
  have hS0 : 0 ∉ S := (Finset.mem_filter.mp hSrest).2
  obtain ⟨U, hU, hUK⟩ := Finset.mem_image.mp hKall
  have hSU : S ∈ squareFibre U := by
    rw [hUK]
    exact hSK
  have hS3 : S.card = 3 := ((mem_squareFibre U S).mp hSU).1
  have hKS : squareFibre S = K :=
    allSquareFibres_squareFibre_member K hKall S hSK
  refine ⟨hS3, hS0, ?_⟩
  simpa only [hKS] using hKF.symm





/-- No ordered pair belongs to two distinct restricted fibres. -/
private theorem zeroFreeFibre_offDiag_pairwiseDisjoint :
    ((zeroFreeFullFibres : Finset (Finset (Finset G))) : Set _).PairwiseDisjoint
      (fun F : Finset (Finset G) => F.offDiag) := by
  intro F hF K hK hne
  apply Finset.disjoint_left.mpr
  intro p hpF hpK
  have hSF : p.1 ∈ F := (Finset.mem_offDiag.mp hpF).1
  have hSK : p.1 ∈ K := (Finset.mem_offDiag.mp hpK).1
  have hFE := (zeroFreeFibre_eq_of_mem F hF p.1 hSF).2.2
  have hKE := (zeroFreeFibre_eq_of_mem K hK p.1 hSK).2.2
  exact hne (hFE.trans hKE.symm)

/-- Each restricted fibre contributes twice its number of unordered
two-subsets, including the zero contribution of fibres of size 0 or 1. -/
private theorem offDiag_card_eq_twice_choose
    (F : Finset (Finset G)) :
    F.offDiag.card = 2 * F.card.choose 2 := by
  calc
    F.offDiag.card =
        2 * (F.offDiag.image (Function.uncurry Sym2.mk)).card :=
      (Sym2.two_mul_card_image_offDiag F).symm
    _ = 2 * F.card.choose 2 :=
      congrArg (fun n : ℕ => 2 * n) (Sym2.card_image_offDiag F)

/-- The second binomial moment counts exactly half the common-fibre
collision darts. No numerical STROBO formula is involved. -/
theorem p2m_local_zeroFreeCollisionDarts_card_eq_twice_moment :
    (zeroFreeCollisionDarts (G := G)).card =
      2 * ∑ F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))),
        F.card.choose 2 := by
  classical
  calc
    (zeroFreeCollisionDarts (G := G)).card =
        ((zeroFreeFullFibres : Finset (Finset (Finset G))).biUnion
          (fun F => F.offDiag)).card :=
      congrArg Finset.card zeroFreeCollisionDarts_eq_fibre_biUnion
    _ = ∑ F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))),
        F.offDiag.card :=
      Finset.card_biUnion zeroFreeFibre_offDiag_pairwiseDisjoint
    _ = ∑ F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))),
        2 * F.card.choose 2 := by
      apply Finset.sum_congr rfl
      intro F _
      exact offDiag_card_eq_twice_choose F
    _ = 2 * ∑ F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))),
        F.card.choose 2 := by
      rw [Finset.mul_sum]













end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.zeroFreeCollisionDarts.{p2m_u_0} G inst inst_1 inst_2))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Finset.sum.{p2m_u_0, 0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) Nat Nat.instAddCommMonoid
        (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) fun F =>
        Nat.choose (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) F)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeCollisionDarts_card_eq_twice_moment

