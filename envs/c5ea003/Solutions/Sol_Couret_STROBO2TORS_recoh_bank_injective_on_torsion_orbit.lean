-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_bank_injective_on_torsion_orbit
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:54.833332+00:00
-- url     : https://prove2.me/submissions/65aec9c9-0bee-4676-8ba5-7b251558c601

import Aesop
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Data.Finite.Card

set_option autoImplicit false

/-!
Character banks chosen after the labelled ordered square has been observed.
The bank may depend on the complete square fibre, but is fixed on that fibre.
The ordinary fibre needs the two-torsion rank many character slots.  An
exceptional fibre needs at most one additional character slot, independently
of the three-torsion rank of the ambient finite abelian group.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- Nonvanishing coefficients and two-torsion separation make a bank injective
on the translation orbit of one fixed support. -/
theorem p2m_local_recoh_bank_injective_on_torsion_orbit
    {I : Type*} (bank : I → AddChar G ℂ) (S : Finset G)
    (hnonzero : ∀ i : I, recohSupportProbe (bank i) S ≠ 0)
    (hsep : ∀ u : G, u + u = 0 → (∀ i : I, bank i u = 1) → u = 0) :
    Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
      (torsionOrbit S) := by
  intro T hT U hU heq
  obtain ⟨u, hu, ht⟩ := (mem_torsionOrbit S T).mp hT
  obtain ⟨v, hv, hUeq⟩ := (mem_torsionOrbit S U).mp hU
  have hvalues : ∀ i : I, bank i u = bank i v := by
    intro i
    apply mul_right_cancel₀ (hnonzero i)
    simpa only [ht, hUeq, recoh_support_probe_translate] using congrFun heq i
  have huv : (u + v) + (u + v) = 0 := by
    calc
      (u + v) + (u + v) = (u + u) + (v + v) := by abel
      _ = 0 := by simp [hu, hv]
  have huv0 : u + v = 0 := by
    apply hsep (u + v) huv
    intro i
    calc
      bank i (u + v) = bank i u * bank i v := (bank i).map_add_eq_mul u v
      _ = bank i v * bank i v := by rw [hvalues i]
      _ = bank i (v + v) := ((bank i).map_add_eq_mul v v).symm
      _ = 1 := by rw [hv, (bank i).map_zero_eq_one]
  have huv_eq : u = v := by
    calc
      u = (u + v) + v := by simp [add_assoc, hv]
      _ = v := by rw [huv0]; simp
  rw [ht, hUeq, huv_eq]















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
  (S : Finset.{p2m_u_0} G),
  (∀ (i : I),
      @Ne.{1} Complex (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) S)
        (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero))) →
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
      @Set.InjOn.{p2m_u_0, p2m_u_1} (Finset.{p2m_u_0} G) (I → Complex)
        (fun T i => @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) T)
        (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
          (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_bank_injective_on_torsion_orbit

