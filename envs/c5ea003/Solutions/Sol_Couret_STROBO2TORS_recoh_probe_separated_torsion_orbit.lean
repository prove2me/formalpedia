-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_probe_separated_torsion_orbit
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:00.741088+00:00
-- url     : https://prove2.me/submissions/4f371e8f-0cc1-4967-b008-11a59212d547

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_ordinary_probe_distance
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_probe_is_sign
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







/-- Translation by two-torsion preserves every character amplitude. -/
theorem recoh_torsion_translate_probe_norm (chi : AddChar G ℂ)
    (S : Finset G) (u : G) (hu : u + u = 0) :
    ‖recohSupportProbe chi (translateSupport S u)‖ =
      ‖recohSupportProbe chi S‖ := by
  rw [recoh_support_probe_translate]
  rcases recoh_two_torsion_probe_is_sign chi chi.map_add_eq_mul
    chi.map_zero_eq_one u hu with h | h
  · simp [h]
  · simp [h]





variable [Fintype G]

/-- An amplitude bound need only be checked on one orbit representative. -/
theorem p2m_local_recoh_probe_separated_torsion_orbit
    {I : Type*} (bank : I → AddChar G ℂ) (S : Finset G) (a : ℝ)
    (hamp : ∀ i, a ≤ ‖recohSupportProbe (bank i) S‖)
    (hsep : ∀ u : G, u + u = 0 → (∀ i, bank i u = 1) → u = 0) :
    RecohProbeSeparated bank (torsionOrbit S) (2 * a) := by
  intro T hT U hU hTU
  have hord : OrdinaryPartner T U := by
    obtain ⟨u, hu, ht⟩ := (mem_torsionOrbit S T).mp hT
    obtain ⟨v, hv, hUeq⟩ := (mem_torsionOrbit S U).mp hU
    refine ⟨u + v, ?_, ?_⟩
    · calc
        (u + v) + (u + v) = (u + u) + (v + v) := by abel
        _ = 0 := by rw [hu, hv, zero_add]
    · rw [ht, translateSupport_add]
      simpa only [← add_assoc, hu, zero_add] using hUeq
  apply recoh_ordinary_probe_distance bank T U a ?_ hsep hord hTU
  intro i
  obtain ⟨u, hu, ht⟩ := (mem_torsionOrbit S T).mp hT
  rw [ht, recoh_torsion_translate_probe_norm (bank i) S u hu]
  exact hamp i













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
  (S : Finset.{p2m_u_0} G) (a : Real),
  (∀ (i : I),
      @LE.le.{0} Real Real.instLE a
        (@Norm.norm.{0} Complex Complex.instNorm (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) S))) →
    (∀ (u : G),
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
          (∀ (i : I),
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
                  (bank i) u)
                (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
            @Eq.{p2m_u_0 + 1} G u
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))) →
      @Couret.STROBO2TORS.RecohProbeSeparated.{p2m_u_0, p2m_u_1} G inst I bank
        (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          a) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_probe_separated_torsion_orbit

