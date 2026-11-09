-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_exceptional_probe_distance_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:51.171733+00:00
-- url     : https://prove2.me/submissions/049ee8d2-46bd-462a-8e54-db578a9f5fb2

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_exceptional_normal_form
import Theorems.Thm_Couret_STROBO2TORS_recoh_finite_character_norm_one
import Theorems.Thm_Couret_STROBO2TORS_recoh_opposite_probe_distance
import Theorems.Thm_Couret_STROBO2TORS_recoh_stability_cubic_reading_norm
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15

set_option autoImplicit false

/-!
Exact separation constants in the exceptional normal form.  Binary probes
have amplitudes one or three, and a detecting ternary probe separates the
two orbits by exactly twice the square root of three.  The two-torsion pair
inside the normal form supplies a matching universal upper bound of two.
-/

namespace Couret.STROBO2TORS

/-- A nontrivial cubic root satisfies its quadratic cyclotomic relation. -/
theorem recoh_stability_cubic_relation (z : ℂ) (hz : z ^ 3 = 1) (hne : z ≠ 1) :
    z ^ 2 + z + 1 = 0 := by
  have hprod : (z - 1) * (z ^ 2 + z + 1) = 0 := by
    calc
      (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 := by ring
      _ = 0 := by rw [hz]; ring
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)



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

omit [DecidableEq G] in
/-- Character values at an order-three direction are cubic roots. -/
theorem recoh_three_torsion_character_cube (chi : AddChar G ℂ)
    (v : G) (hv : (v + v) + v = 0) : (chi v) ^ 3 = 1 := by
  have h := congrArg chi hv
  simpa only [chi.map_add_eq_mul, chi.map_zero_eq_one, pow_succ, pow_zero,
    one_mul] using h

variable [Fintype G]





/-- Exact amplitude of a detecting ternary character on one representative. -/
theorem recoh_ternary_param_probe_norm (chi : AddChar G ℂ) (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0)
    (hcd : chi d = 1) (hcv : chi v ≠ 1) :
    ‖recohSupportProbe chi (paramSupport ((a, d), v))‖ = Real.sqrt 3 := by
  rw [recoh_param_probe_formula chi a d v hd hd0 hv hv0, hcd]
  have h : 1 + chi v * (1 + 1) = 1 + 2 * chi v := by ring
  rw [h, norm_mul, recoh_finite_character_norm_one, one_mul]
  exact recoh_stability_cubic_reading_norm (chi v) (recoh_three_torsion_character_cube chi v hv) hcv

/-- The two reflected exceptional readings are opposites. -/
theorem recoh_ternary_param_probe_opposite (chi : AddChar G ℂ) (a d v u : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0)
    (hcd : chi d = 1) (hcu : chi u = 1) (hcv : chi v ≠ 1) :
    recohSupportProbe chi (translateSupport (paramSupport ((a, d), -v)) u) =
      -recohSupportProbe chi (paramSupport ((a, d), v)) := by
  rw [recoh_support_probe_translate, hcu, one_mul,
    recoh_param_probe_formula chi a d (-v) hd hd0 (three_torsion_neg v hv) (neg_ne_zero.mpr hv0),
    recoh_param_probe_formula chi a d v hd hd0 hv hv0, hcd]
  have hnv : chi (-v) = (chi v) ^ 2 := by
    rw [← eq_neg_of_add_eq_zero_left hv, chi.map_add_eq_mul, pow_two]
  rw [hnv]
  have hpoly := recoh_stability_cubic_relation (chi v)
    (recoh_three_torsion_character_cube chi v hv) hcv
  linear_combination 2 * chi a * hpoly

/-- The ternary separation is exact and is unchanged by the unknown
two-torsion translation of either representative. -/
theorem recoh_ternary_param_probe_distance (chi : AddChar G ℂ) (a d v u : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0)
    (hcd : chi d = 1) (hcu : chi u = 1) (hcv : chi v ≠ 1) :
    ‖recohSupportProbe chi (paramSupport ((a, d), v)) -
      recohSupportProbe chi (translateSupport (paramSupport ((a, d), -v)) u)‖ =
      2 * Real.sqrt 3 := by
  rw [recoh_ternary_param_probe_opposite chi a d v u hd hd0 hv hv0 hcd hcu hcv,
    recoh_opposite_probe_distance,
    recoh_ternary_param_probe_norm chi a d v hd hd0 hv hv0 hcd hcv]

/-- In an exceptional collision, any differing character that is trivial
on two-torsion already has the precise distance 2 sqrt 3. -/
theorem p2m_local_recoh_exceptional_probe_distance_of_ne (chi : AddChar G ℂ)
    (S T : Finset G) (he : ExceptionalPartner S T)
    (htrivial : ∀ u : G, u + u = 0 → chi u = 1)
    (hne : recohSupportProbe chi S ≠ recohSupportProbe chi T) :
    ‖recohSupportProbe chi S - recohSupportProbe chi T‖ = 2 * Real.sqrt 3 := by
  obtain ⟨a, d, v, u, hd, hd0, hv, hv0, hu, hs, ht⟩ := recoh_exceptional_normal_form S T he
  have hcv : chi v ≠ 1 := by
    intro hcv
    have hcnv : chi (-v) = 1 := by
      have h := (chi.map_add_eq_mul v (-v)).symm
      simpa [hcv] using h
    apply hne
    rw [hs, ht, recoh_support_probe_translate, htrivial u hu, one_mul,
      recoh_param_probe_formula chi a d v hd hd0 hv hv0,
      recoh_param_probe_formula chi a d (-v) hd hd0 (three_torsion_neg v hv) (neg_ne_zero.mpr hv0),
      hcv, hcnv]
  rw [hs, ht]
  exact recoh_ternary_param_probe_distance chi a d v u hd hd0 hv hv0
    (htrivial d hd) (htrivial u hu) hcv









end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G]
  (chi :
    @AddChar.{p2m_u_0, 0} G
      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (S T : Finset.{p2m_u_0} G),
  @Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T →
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
      @Ne.{1} Complex (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi S)
          (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi T) →
        @Eq.{1} Real
          (@Norm.norm.{0} Complex Complex.instNorm
            (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
              (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi S)
              (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi T)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (Real.sqrt
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_exceptional_probe_distance_of_ne

