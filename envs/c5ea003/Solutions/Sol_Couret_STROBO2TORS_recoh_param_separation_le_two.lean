-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_param_separation_le_two
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:55:58.046667+00:00
-- url     : https://prove2.me/submissions/4d6883f1-5920-48dc-a50e-ba116430e207

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
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_opposite_probe_distance
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_probe_is_sign
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_free_of_card_three
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15

set_option autoImplicit false

/-!
Exact separation constants in the exceptional normal form.  Binary probes
have amplitudes one or three, and a detecting ternary probe separates the
two orbits by exactly twice the square root of three.  The two-torsion pair
inside the normal form supplies a matching universal upper bound of two.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The normal-form coefficient, before imposing any primary restriction. -/
theorem recoh_param_probe_formula (chi : AddChar G ℂ) (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    recohSupportProbe chi (paramSupport ((a, d), v)) =
      chi a * (1 + chi v * (1 + chi d)) := by
  have hcard := paramSupport_card a d v hd hd0 hv hv0
  obtain ⟨hab, hac, hbc⟩ := displayed_three_distinct a (a + v) ((a + v) + d) hcard
  change recohSupportProbe chi {a, a + v, (a + v) + d} = _
  rw [recoh_support_probe_three chi _ _ _ hab hac hbc]
  simp only [chi.map_add_eq_mul]
  ring



variable [Fintype G]















/-- The involution from the exceptional normal form supplies a pair whose
distance is either zero or two for every character of the finite group. -/
theorem recoh_param_torsion_probe_distance
    (chi : AddChar G ℂ) (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    ‖recohSupportProbe chi (paramSupport ((a, d), v)) -
      recohSupportProbe chi (translateSupport (paramSupport ((a, d), v)) d)‖ = 0 ∨
    ‖recohSupportProbe chi (paramSupport ((a, d), v)) -
      recohSupportProbe chi (translateSupport (paramSupport ((a, d), v)) d)‖ = 2 := by
  rw [recoh_support_probe_translate]
  rcases recoh_two_torsion_probe_is_sign chi chi.map_add_eq_mul chi.map_zero_eq_one
    d hd with hpos | hneg
  · left
    simp [hpos]
  · right
    rw [hneg, neg_one_mul, recoh_opposite_probe_distance,
      recoh_param_probe_formula chi a d v hd hd0 hv hv0, hneg]
    simp

/-- The distance-two upper bound applies to every bank on every
exceptional normal-form fibre, without a cardinality restriction on it. -/
theorem p2m_local_recoh_param_separation_le_two
    {I : Type*} (bank : I → AddChar G ℂ) (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0)
    (δ : ℝ) (hsep : RecohProbeSeparated bank
      (squareFibre (paramSupport ((a, d), v))) δ) : δ ≤ 2 := by
  let S := paramSupport ((a, d), v)
  let T := translateSupport S d
  have hcard : S.card = 3 := paramSupport_card a d v hd hd0 hv hv0
  have hSmem : S ∈ squareFibre S := (mem_squareFibre S S).mpr ⟨hcard, fun _ => rfl⟩
  have hTmem : T ∈ squareFibre S := torsionOrbit_subset_fibre S hcard
    ((mem_torsionOrbit S T).mpr ⟨d, hd, rfl⟩)
  have hST : S ≠ T := by
    intro h
    exact hd0 (translateSupport_free_of_card_three S hcard d hd h.symm)
  obtain ⟨i, hi⟩ := hsep S hSmem T hTmem hST
  have hupper : ‖recohSupportProbe (bank i) S - recohSupportProbe (bank i) T‖ ≤ 2 := by
    rcases recoh_param_torsion_probe_distance (bank i) a d v hd hd0 hv hv0 with h | h
    · change ‖recohSupportProbe (bank i) (paramSupport ((a, d), v)) -
        recohSupportProbe (bank i) (translateSupport (paramSupport ((a, d), v)) d)‖ ≤ 2
      rw [h]; norm_num
    · exact le_of_eq h
  exact hi.trans hupper



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
  (a d v : G),
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
      @Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              v v)
            v)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
        @Ne.{p2m_u_0 + 1} G v
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
          ∀ (δ : Real),
            @Couret.STROBO2TORS.RecohProbeSeparated.{p2m_u_0, p2m_u_1} G inst I bank
                (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2
                  (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                    (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d)
                      v)))
                δ →
              @LE.le.{0} Real Real.instLE δ
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_param_separation_le_two

