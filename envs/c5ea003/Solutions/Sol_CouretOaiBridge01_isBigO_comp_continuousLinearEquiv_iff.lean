-- Prove2me | solution 1 for CouretOaiBridge01.isBigO_comp_continuousLinearEquiv_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:46:37.551204+00:00
-- url     : https://prove2.me/submissions/afd036d8-95e4-42e1-929c-d1c9f811cf18

import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Analysis.Normed.Operator.Asymptotics

open Filter
open Asymptotics

/-!
# COURET–OAI–BRIDGE–01 / A0 — Generic no-gain under a continuous linear equivalence

This file isolates the functional-analytic core of the fixed-modulus no-gain statement.
It is intentionally independent of U(30), Möbius sums, Dirichlet characters, and Mellin
transforms.

A continuous linear equivalence and its inverse are both bounded. Consequently, composing
a family with such an equivalence preserves its Big-O class.

Research status:
* exact abstract theorem;
* no Riemann-hypothesis claim;
* no novelty claim;
* intended as the zero-sorry base layer for BRIDGE01-A.
-/

namespace CouretOaiBridge01

/--
Composing a family with a continuous linear self-equivalence preserves any Big-O bound.

No finite-dimensional hypothesis is needed.
-/
theorem p2m_local_isBigO_comp_continuousLinearEquiv_iff
    {𝕜 E G α : Type*}
    [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup G]
    (e : E ≃L[𝕜] E)
    (F : α → E)
    (g : α → G)
    (l : Filter α) :
    (fun x => e (F x)) =O[l] g ↔ F =O[l] g := by
  constructor
  · intro h
    exact (e.isBigO_comp_rev F l).trans h
  · intro h
    exact (e.isBigO_comp F l).trans h

end CouretOaiBridge01

universe p2m_u_0 p2m_u_1 p2m_u_2 p2m_u_3
theorem solution : ∀ {𝕜 : Type p2m_u_0} {E : Type p2m_u_1} {G : Type p2m_u_2} {α : Type p2m_u_3}
  [inst : NontriviallyNormedField.{p2m_u_0} 𝕜] [inst_1 : SeminormedAddCommGroup.{p2m_u_1} E]
  [inst_2 : @NormedSpace.{p2m_u_0, p2m_u_1} 𝕜 E (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst) inst_1]
  [inst_3 : SeminormedAddCommGroup.{p2m_u_2} G]
  (e :
    @ContinuousLinearEquiv.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_1} 𝕜 𝕜
      (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
        (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
          (@Field.toSemifield.{p2m_u_0} 𝕜
            (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))
      (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
        (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
          (@Field.toSemifield.{p2m_u_0} 𝕜
            (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))
      (@RingHom.id.{p2m_u_0} 𝕜
        (@Semiring.toNonAssocSemiring.{p2m_u_0} 𝕜
          (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
            (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
              (@Field.toSemifield.{p2m_u_0} 𝕜
                (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))))
      (@RingHom.id.{p2m_u_0} 𝕜
        (@Semiring.toNonAssocSemiring.{p2m_u_0} 𝕜
          (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
            (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
              (@Field.toSemifield.{p2m_u_0} 𝕜
                (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))))
      (@RingHomInvPair.ids.{p2m_u_0} 𝕜
        (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
          (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
            (@Field.toSemifield.{p2m_u_0} 𝕜
              (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst))))))
      (@RingHomInvPair.ids.{p2m_u_0} 𝕜
        (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
          (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
            (@Field.toSemifield.{p2m_u_0} 𝕜
              (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst))))))
      E
      (@UniformSpace.toTopologicalSpace.{p2m_u_1} E
        (@PseudoMetricSpace.toUniformSpace.{p2m_u_1} E
          (@SeminormedAddCommGroup.toPseudoMetricSpace.{p2m_u_1} E inst_1)))
      (@AddCommGroup.toAddCommMonoid.{p2m_u_1} E (@SeminormedAddCommGroup.toAddCommGroup.{p2m_u_1} E inst_1)) E
      (@UniformSpace.toTopologicalSpace.{p2m_u_1} E
        (@PseudoMetricSpace.toUniformSpace.{p2m_u_1} E
          (@SeminormedAddCommGroup.toPseudoMetricSpace.{p2m_u_1} E inst_1)))
      (@AddCommGroup.toAddCommMonoid.{p2m_u_1} E (@SeminormedAddCommGroup.toAddCommGroup.{p2m_u_1} E inst_1))
      (@NormedSpace.toModule.{p2m_u_0, p2m_u_1} 𝕜 E (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst) inst_1
        inst_2)
      (@NormedSpace.toModule.{p2m_u_0, p2m_u_1} 𝕜 E (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst) inst_1
        inst_2))
  (F : α → E) (g : α → G) (l : Filter.{p2m_u_3} α),
  Iff
    (@Asymptotics.IsBigO.{p2m_u_3, p2m_u_1, p2m_u_2} α E G (@SeminormedAddCommGroup.toNorm.{p2m_u_1} E inst_1)
      (@SeminormedAddCommGroup.toNorm.{p2m_u_2} G inst_3) l
      (fun x =>
        @DFunLike.coe.{p2m_u_1 + 1, p2m_u_1 + 1, p2m_u_1 + 1}
          (@ContinuousLinearEquiv.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_1} 𝕜 𝕜
            (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
              (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                (@Field.toSemifield.{p2m_u_0} 𝕜
                  (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))
            (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
              (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                (@Field.toSemifield.{p2m_u_0} 𝕜
                  (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))
            (@RingHom.id.{p2m_u_0} 𝕜
              (@Semiring.toNonAssocSemiring.{p2m_u_0} 𝕜
                (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                  (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                    (@Field.toSemifield.{p2m_u_0} 𝕜
                      (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))))
            (@RingHom.id.{p2m_u_0} 𝕜
              (@Semiring.toNonAssocSemiring.{p2m_u_0} 𝕜
                (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                  (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                    (@Field.toSemifield.{p2m_u_0} 𝕜
                      (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))))
            (@RingHomInvPair.ids.{p2m_u_0} 𝕜
              (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                  (@Field.toSemifield.{p2m_u_0} 𝕜
                    (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst))))))
            (@RingHomInvPair.ids.{p2m_u_0} 𝕜
              (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                  (@Field.toSemifield.{p2m_u_0} 𝕜
                    (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst))))))
            E
            (@UniformSpace.toTopologicalSpace.{p2m_u_1} E
              (@PseudoMetricSpace.toUniformSpace.{p2m_u_1} E
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{p2m_u_1} E inst_1)))
            (@AddCommGroup.toAddCommMonoid.{p2m_u_1} E (@SeminormedAddCommGroup.toAddCommGroup.{p2m_u_1} E inst_1)) E
            (@UniformSpace.toTopologicalSpace.{p2m_u_1} E
              (@PseudoMetricSpace.toUniformSpace.{p2m_u_1} E
                (@SeminormedAddCommGroup.toPseudoMetricSpace.{p2m_u_1} E inst_1)))
            (@AddCommGroup.toAddCommMonoid.{p2m_u_1} E (@SeminormedAddCommGroup.toAddCommGroup.{p2m_u_1} E inst_1))
            (@NormedSpace.toModule.{p2m_u_0, p2m_u_1} 𝕜 E (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)
              inst_1 inst_2)
            (@NormedSpace.toModule.{p2m_u_0, p2m_u_1} 𝕜 E (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)
              inst_1 inst_2))
          E (fun x => E)
          (@EquivLike.toFunLike.{p2m_u_1 + 1, p2m_u_1 + 1, p2m_u_1 + 1}
            (@ContinuousLinearEquiv.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_1} 𝕜 𝕜
              (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                  (@Field.toSemifield.{p2m_u_0} 𝕜
                    (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))
              (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                  (@Field.toSemifield.{p2m_u_0} 𝕜
                    (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))
              (@RingHom.id.{p2m_u_0} 𝕜
                (@Semiring.toNonAssocSemiring.{p2m_u_0} 𝕜
                  (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                    (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                      (@Field.toSemifield.{p2m_u_0} 𝕜
                        (@NormedField.toField.{p2m_u_0} 𝕜
                          (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))))
              (@RingHom.id.{p2m_u_0} 𝕜
                (@Semiring.toNonAssocSemiring.{p2m_u_0} 𝕜
                  (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                    (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                      (@Field.toSemifield.{p2m_u_0} 𝕜
                        (@NormedField.toField.{p2m_u_0} 𝕜
                          (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))))
              (@RingHomInvPair.ids.{p2m_u_0} 𝕜
                (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                  (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                    (@Field.toSemifield.{p2m_u_0} 𝕜
                      (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst))))))
              (@RingHomInvPair.ids.{p2m_u_0} 𝕜
                (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                  (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                    (@Field.toSemifield.{p2m_u_0} 𝕜
                      (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst))))))
              E
              (@UniformSpace.toTopologicalSpace.{p2m_u_1} E
                (@PseudoMetricSpace.toUniformSpace.{p2m_u_1} E
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{p2m_u_1} E inst_1)))
              (@AddCommGroup.toAddCommMonoid.{p2m_u_1} E (@SeminormedAddCommGroup.toAddCommGroup.{p2m_u_1} E inst_1)) E
              (@UniformSpace.toTopologicalSpace.{p2m_u_1} E
                (@PseudoMetricSpace.toUniformSpace.{p2m_u_1} E
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{p2m_u_1} E inst_1)))
              (@AddCommGroup.toAddCommMonoid.{p2m_u_1} E (@SeminormedAddCommGroup.toAddCommGroup.{p2m_u_1} E inst_1))
              (@NormedSpace.toModule.{p2m_u_0, p2m_u_1} 𝕜 E (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)
                inst_1 inst_2)
              (@NormedSpace.toModule.{p2m_u_0, p2m_u_1} 𝕜 E (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)
                inst_1 inst_2))
            E E
            (@ContinuousLinearEquiv.equivLike.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_1} 𝕜 𝕜
              (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                  (@Field.toSemifield.{p2m_u_0} 𝕜
                    (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))
              (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                  (@Field.toSemifield.{p2m_u_0} 𝕜
                    (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))
              (@RingHom.id.{p2m_u_0} 𝕜
                (@Semiring.toNonAssocSemiring.{p2m_u_0} 𝕜
                  (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                    (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                      (@Field.toSemifield.{p2m_u_0} 𝕜
                        (@NormedField.toField.{p2m_u_0} 𝕜
                          (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))))
              (@RingHom.id.{p2m_u_0} 𝕜
                (@Semiring.toNonAssocSemiring.{p2m_u_0} 𝕜
                  (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                    (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                      (@Field.toSemifield.{p2m_u_0} 𝕜
                        (@NormedField.toField.{p2m_u_0} 𝕜
                          (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)))))))
              (@RingHomInvPair.ids.{p2m_u_0} 𝕜
                (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                  (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                    (@Field.toSemifield.{p2m_u_0} 𝕜
                      (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst))))))
              (@RingHomInvPair.ids.{p2m_u_0} 𝕜
                (@DivisionSemiring.toSemiring.{p2m_u_0} 𝕜
                  (@Semifield.toDivisionSemiring.{p2m_u_0} 𝕜
                    (@Field.toSemifield.{p2m_u_0} 𝕜
                      (@NormedField.toField.{p2m_u_0} 𝕜 (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst))))))
              E
              (@UniformSpace.toTopologicalSpace.{p2m_u_1} E
                (@PseudoMetricSpace.toUniformSpace.{p2m_u_1} E
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{p2m_u_1} E inst_1)))
              (@AddCommGroup.toAddCommMonoid.{p2m_u_1} E (@SeminormedAddCommGroup.toAddCommGroup.{p2m_u_1} E inst_1)) E
              (@UniformSpace.toTopologicalSpace.{p2m_u_1} E
                (@PseudoMetricSpace.toUniformSpace.{p2m_u_1} E
                  (@SeminormedAddCommGroup.toPseudoMetricSpace.{p2m_u_1} E inst_1)))
              (@AddCommGroup.toAddCommMonoid.{p2m_u_1} E (@SeminormedAddCommGroup.toAddCommGroup.{p2m_u_1} E inst_1))
              (@NormedSpace.toModule.{p2m_u_0, p2m_u_1} 𝕜 E (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)
                inst_1 inst_2)
              (@NormedSpace.toModule.{p2m_u_0, p2m_u_1} 𝕜 E (@NontriviallyNormedField.toNormedField.{p2m_u_0} 𝕜 inst)
                inst_1 inst_2)))
          e (F x))
      g)
    (@Asymptotics.IsBigO.{p2m_u_3, p2m_u_1, p2m_u_2} α E G (@SeminormedAddCommGroup.toNorm.{p2m_u_1} E inst_1)
      (@SeminormedAddCommGroup.toNorm.{p2m_u_2} G inst_3) l F g) := @_root_.CouretOaiBridge01.p2m_local_isBigO_comp_continuousLinearEquiv_iff

