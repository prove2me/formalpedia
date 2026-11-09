-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_probe_constant_on_torsion_orbit
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:52.086059+00:00
-- url     : https://prove2.me/submissions/152faf40-b699-4fc6-8a02-90b04c16266c

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



/-- A character trivial on two-torsion is constant on every torsion orbit. -/
theorem p2m_local_recoh_probe_constant_on_torsion_orbit
    (chi : AddChar G ℂ)
    (htrivial : ∀ u : G, u + u = 0 → chi u = 1)
    (S T : Finset G) (hT : T ∈ torsionOrbit S) :
    recohSupportProbe chi T = recohSupportProbe chi S := by
  obtain ⟨u, hu, ht⟩ := (mem_torsionOrbit S T).mp hT
  rw [ht, recoh_support_probe_translate, htrivial u hu, one_mul]













end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G]
  (chi :
    @AddChar.{p2m_u_0, 0} G
      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
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
    ∀ (S T : Finset.{p2m_u_0} G),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
          (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S) T →
        @Eq.{1} Complex (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi T)
          (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_probe_constant_on_torsion_orbit

