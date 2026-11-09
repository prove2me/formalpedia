-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_probe_separated_two_orbits
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:50.131541+00:00
-- url     : https://prove2.me/submissions/cf08c910-acab-40cc-aa49-ac757b98cc4f

import Aesop
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_constant_on_torsion_orbit
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
Quantitative separation of character readings.  A separation statement uses
an existential coordinate; no finite maximum, nonempty bank, or nontrivial
fibre is silently assumed.  In particular singleton fibres and empty banks
are handled by the same definition.
-/

namespace Couret.STROBO2TORS



variable {G : Type*} [AddCommGroup G] [DecidableEq G]













variable [Fintype G]



/-- Two internally separated torsion orbits are separated by their binary
bank and one character constant on each orbit. -/
theorem p2m_local_recoh_probe_separated_two_orbits
    {I : Type*} (bank : I → AddChar G ℂ) (chi : AddChar G ℂ)
    (S T : Finset G) (δ : ℝ)
    (hS : RecohProbeSeparated bank (torsionOrbit S) δ)
    (hT : RecohProbeSeparated bank (torsionOrbit T) δ)
    (htrivial : ∀ u : G, u + u = 0 → chi u = 1)
    (hcross : δ ≤ ‖recohSupportProbe chi S - recohSupportProbe chi T‖) :
    RecohProbeSeparated (Sum.elim bank (fun _ : Unit => chi))
      (torsionOrbit S ∪ torsionOrbit T) δ := by
  intro B hB C hC hBC
  rcases Finset.mem_union.mp hB with hB | hB
  · rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨i, hi⟩ := hS B hB C hC hBC
      exact ⟨Sum.inl i, hi⟩
    · refine ⟨Sum.inr (), ?_⟩
      change δ ≤ ‖recohSupportProbe chi B - recohSupportProbe chi C‖
      rw [recoh_probe_constant_on_torsion_orbit chi htrivial S B hB,
        recoh_probe_constant_on_torsion_orbit chi htrivial T C hC]
      exact hcross
  · rcases Finset.mem_union.mp hC with hC | hC
    · refine ⟨Sum.inr (), ?_⟩
      change δ ≤ ‖recohSupportProbe chi B - recohSupportProbe chi C‖
      rw [recoh_probe_constant_on_torsion_orbit chi htrivial T B hB,
        recoh_probe_constant_on_torsion_orbit chi htrivial S C hC, norm_sub_rev]
      exact hcross
    · obtain ⟨i, hi⟩ := hT B hB C hC hBC
      exact ⟨Sum.inl i, hi⟩











end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] {I : Type p2m_u_1}
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (chi :
    @AddChar.{p2m_u_0, 0} G
      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (S T : Finset.{p2m_u_0} G) (δ : Real),
  @Couret.STROBO2TORS.RecohProbeSeparated.{p2m_u_0, p2m_u_1} G inst I bank
      (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S) δ →
    @Couret.STROBO2TORS.RecohProbeSeparated.{p2m_u_0, p2m_u_1} G inst I bank
        (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 T) δ →
      (∀ (u : G),
          @Eq.{p2m_u_0 + 1} G
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                u u)
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
            @Eq.{1} Complex
              (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                (@AddChar.{p2m_u_0, 0} G
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                G (fun x => Complex)
                (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                chi u)
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
        @LE.le.{0} Real Real.instLE δ
            (@Norm.norm.{0} Complex Complex.instNorm
              (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi S)
                (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi T))) →
          @Couret.STROBO2TORS.RecohProbeSeparated.{p2m_u_0, p2m_u_1} G inst (Sum.{p2m_u_1, 0} I Unit)
            (@Sum.elim.{p2m_u_1, 0, p2m_u_0 + 1} I Unit
              (@AddChar.{p2m_u_0, 0} G
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
              bank fun x => chi)
            (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@Finset.instUnion.{p2m_u_0} (Finset.{p2m_u_0} G) fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
              (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S)
              (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 T))
            δ := @_root_.Couret.STROBO2TORS.p2m_local_recoh_probe_separated_two_orbits

