-- Prove2me | solution 1 for Couret.STROBO2TORS.triple_translation_free
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:32:16.658455+00:00
-- url     : https://prove2.me/submissions/b92bf5e8-b19f-4b00-8c0e-b71fae1419b0

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_triple_sum_translate
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





















/-- Unordered three-point support has sum a+b+c when entries are distinct. -/
private theorem sum_three
    (a b c : G) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset G).sum id = a + b + c := by
  simp [hab, hac, hbc, add_assoc, add_comm, add_left_comm]

/--
No nonzero 2-torsion element can fix a three-point support under translation.
Equivalently, the action of G[2] on three-element supports is free.
-/
theorem p2m_local_triple_translation_free
    (a b c u : G) (hu : u + u = 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (heq : ({a + u, b + u, c + u} : Finset G) =
      ({a, b, c} : Finset G)) : u = 0 := by
  have habu : a + u ≠ b + u := by
    intro h
    exact hab (add_right_cancel h)
  have hacu : a + u ≠ c + u := by
    intro h
    exact hac (add_right_cancel h)
  have hbcu : b + u ≠ c + u := by
    intro h
    exact hbc (add_right_cancel h)
  have hsum : (a + u) + (b + u) + (c + u) = a + b + c := by
    have hs := congrArg (fun s : Finset G => s.sum id) heq
    change ({a + u, b + u, c + u} : Finset G).sum id =
      ({a, b, c} : Finset G).sum id at hs
    rw [sum_three (a + u) (b + u) (c + u) habu hacu hbcu,
        sum_three a b c hab hac hbc] at hs
    exact hs
  rw [triple_sum_translate a b c u hu] at hsum
  have hzero : (a + b + c) + u = (a + b + c) + 0 := by
    simpa using hsum
  exact add_left_cancel hzero




/-! ## Exceptional cross-matching: constructive ("if") direction -/






/-! ## Algebraic prerequisites for the necessary direction -/






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
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (a b c u : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        u u)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Ne.{p2m_u_0 + 1} G a b →
      @Ne.{p2m_u_0 + 1} G a c →
        @Ne.{p2m_u_0 + 1} G b c →
          @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  a u)
                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    b u)
                  (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      c u))))
              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) b
                  (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                    c))) →
            @Eq.{p2m_u_0 + 1} G u
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) := @_root_.Couret.STROBO2TORS.p2m_local_triple_translation_free

