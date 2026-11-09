-- Prove2me | solution 1 for Couret.STROBO2TORS.two_point_pair_direction
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:30:55.441045+00:00
-- url     : https://prove2.me/submissions/652ebfbe-a2fc-4c6e-9e73-682cfd65a321

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega
import Aesop

set_option autoImplicit false

/-!
STROBO-2TORS: ordered-square classification of three-element finite supports.

This file establishes an assembled equivalence for the actual ordered-square
coefficient of cardinality-three Finsets, with every doubling profile and
relabelling handled internally. Exceptional partners are not related by any
ambient-group translation. It does NOT establish formal cardinality/counting
theorems, independent mathematical validation, or a novelty claim.

The coefficient below is the explicit nine-ordered-pair expansion of the
convolution square of a three-element support {a,b,c}, when its entries are
pairwise distinct. Thus diagonal terms have coefficient 1 and the three
off-diagonal pair sums have coefficient 2.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]




























/-! ## Exceptional cross-matching: constructive ("if") direction -/






/-! ## Algebraic prerequisites for the necessary direction -/

/--
The direction of a two-point H-pair is intrinsic: two equal unordered pairs
{x,x+d} and {y,y+e}, with d,e nonzero and d of order two, have e=d.
This is the elementary reduction needed before matching double-fibre terms.
-/
theorem p2m_local_two_point_pair_direction
    (x y d e : G) (hd : d + d = 0)
    (hd0 : d ≠ 0) (he0 : e ≠ 0)
    (hpairs : ({x, x + d} : Finset G) = ({y, y + e} : Finset G)) :
    e = d := by
  have hy : y = x ∨ y = x + d := by
    have hm : y ∈ ({x, x + d} : Finset G) := by
      rw [hpairs]
      simp
    simpa using hm
  have hye : y + e = x ∨ y + e = x + d := by
    have hm : y + e ∈ ({x, x + d} : Finset G) := by
      rw [hpairs]
      simp
    simpa using hm
  rcases hy with hy | hy
  · rcases hye with hye | hye
    · have hz : e = 0 := by
        have hh : x + e = x + 0 := by simpa [hy] using hye
        exact add_left_cancel hh
      exact (he0 hz).elim
    · have hh : x + e = x + d := by simpa [hy] using hye
      exact add_left_cancel hh
  · rcases hye with hye | hye
    · have h : (x + d) + e = x := by simpa [hy] using hye
      have hde : d + e = 0 := by
        have hh : x + (d + e) = x + 0 := by
          calc
            x + (d + e) = (x + d) + e := by abel
            _ = x := h
            _ = x + 0 := by simp
        exact add_left_cancel hh
      have heqd : e = -d := by
        calc
          e = (d + e) - d := by abel
          _ = -d := by rw [hde]; simp
      have hdneg : -d = d := by
        calc
          -d = d - (d + d) := by abel
          _ = d := by rw [hd]; simp
      exact heqd.trans hdneg
    · have hz : e = 0 := by
        have hh : (x + d) + e = (x + d) + 0 := by
          simpa [hy] using hye
        exact add_left_cancel hh
      exact (he0 hz).elim




/-! ## From arbitrary equal squares to the singleton and residual identities -/
















/-! ## Exhaustiveness of the two residual pair-coset matchings -/
















/-! ## Lifting residual base matching to the two-torsion direction -/








/-! ## Necessary classification in the normalized genuine (1,2) case -/



/-! ## Reconstruction from the three off-diagonal sums -/





/-! ## Profile (1,1,1): parity recovers all diagonals -/







/-! ## Profile (3): the unique odd diagonal has multiplicity three -/







/-! ## Separation of the three profiles -/













/-! ## Raccordement: unnormalized genuine paired triples -/



/-! ## Actual ordered square of finite supports -/























































end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (x y d e : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        d d)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Ne.{p2m_u_0 + 1} G d
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Ne.{p2m_u_0 + 1} G e
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
        @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) x
              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  x d)))
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) y
              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  y e))) →
          @Eq.{p2m_u_0 + 1} G e d := @_root_.Couret.STROBO2TORS.p2m_local_two_point_pair_direction

