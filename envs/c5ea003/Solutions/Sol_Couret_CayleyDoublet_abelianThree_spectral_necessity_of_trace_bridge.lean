-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_spectral_necessity_of_trace_bridge
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:35:33.153819+00:00
-- url     : https://prove2.me/submissions/7f46adf1-b839-43e4-af6c-d0a2b79fe75f

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_witness_of_odd_quotient
import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d

/-!
COU-20 — research branch only, spectral necessity work in progress.

This file is deliberately separate from the certified Core/Family/Abelian/
Spectral/Parity modules. It does not claim a new Lean or GitHub Actions
certificate until it has been compiled against the pinned toolchain.

The cyclic lemma below produces an odd *discriminating* exponent. It is
slightly more general than the canonical candidate |Q|/3: its exponent
need not be the least such one. Directed adjacency and loops are untouched.

The generic rational charpoly-to-all-power-traces theorem is NOT assumed as
proved. The final assembly is explicitly conditional on that missing bridge.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Couret.CayleyNecessity





end Couret.CayleyNecessity

namespace Couret.CayleyDoublet

open Couret.CayleyNecessity

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]







/-- An exact assembly interface for the missing all-power-traces lemma.
This statement is CONDITIONAL: hbridge is NOT derived here from charpoly
equality and therefore this is not the desired unconditional necessity.
The implication alone does not require global generation by a,d,h:
if generation by a,h fails, its first disjunct already holds; if it
succeeds, global generation is automatic. The full IFF still requires
global generation in the sufficient direction. -/
theorem p2m_local_abelianThree_spectral_necessity_of_trace_bridge (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hbridge :
      ∀ n : ℕ,
        (abelianCayleyMatrix (AbelianSource a d h)).charpoly =
          (abelianCayleyMatrix (AbelianTarget a d h)).charpoly →
        Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ n) =
          Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ n))
    (hcospec :
      (abelianCayleyMatrix (AbelianSource a d h)).charpoly =
        (abelianCayleyMatrix (AbelianTarget a d h)).charpoly) :
    AddSubgroup.closure ({a, h} : Set G) ≠ ⊤ ∨
      Even (Nat.card (G ⧸ AddSubgroup.zmultiples h)) := by
  classical
  by_cases hproper : AddSubgroup.closure ({a, h} : Set G) ≠ ⊤
  · exact Or.inl hproper
  · have hfull : AddSubgroup.closure ({a, h} : Set G) = ⊤ :=
      not_ne_iff.mp hproper
    rcases Nat.even_or_odd (Nat.card (G ⧸ AddSubgroup.zmultiples h)) with heven | hodd
    · exact Or.inr heven
    · obtain ⟨n, hdiff⟩ :=
        abelianThree_odd_trace_witness_of_odd_quotient a d h
          hhalf hne horder hfull hodd
      exact (hdiff (hbridge (2 * n + 1) hcospec)).elim



end Couret.CayleyDoublet



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (a d h : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        h h)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Ne.{p2m_u_0 + 1} G h
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Eq.{1} Nat
          (@addOrderOf.{p2m_u_0}
            (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
            (@SubNegMonoid.toAddMonoid.{p2m_u_0}
              (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
              (@AddGroup.toSubNegMonoid.{p2m_u_0}
                (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
                (@QuotientAddGroup.Quotient.addGroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                  (@AddSubgroup.normal_of_isAddCommutative.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@AddCommMagma.to_isCommutative.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))))
            (@QuotientAddGroup.mk.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
              (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h) d))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        (∀ (n : Nat),
            @Eq.{1}
                (@Polynomial.{0} Rat (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
                (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing G inst_1 inst_2
                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                    (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h)))
                (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing G inst_1 inst_2
                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                    (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))) →
              @Eq.{1} Rat
                (@Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                  (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                    (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                    (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                      (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                        (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                          (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                    (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                      (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h))
                    n))
                (@Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                  (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                    (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                    (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                      (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                        (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                          (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                    (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                      (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))
                    n))) →
          @Eq.{1}
              (@Polynomial.{0} Rat (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
              (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing G inst_1 inst_2
                (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                  (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h)))
              (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing G inst_1 inst_2
                (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                  (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))) →
            Or
              (@Ne.{p2m_u_0 + 1} (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@AddSubgroup.closure.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Set.{p2m_u_0} G) (@Set.instInsert.{p2m_u_0} G) a
                    (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Set.{p2m_u_0} G) (@Set.instSingletonSet.{p2m_u_0} G)
                      h)))
                (@Top.top.{p2m_u_0} (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@AddSubgroup.instTop.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
              (@Even.{0} Nat instAddNat
                (Nat.card.{p2m_u_0}
                  (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_spectral_necessity_of_trace_bridge

