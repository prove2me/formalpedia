-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_param_probe_separated_two
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:55:52.683733+00:00
-- url     : https://prove2.me/submissions/165faee7-a81d-45e2-9d99-bfa93359c070

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_finite_character_norm_one
import Theorems.Thm_Couret_STROBO2TORS_recoh_opposite_probe_distance
import Theorems.Thm_Couret_STROBO2TORS_recoh_param_square_fibre_eq
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_separated_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_separated_two_orbits
import Theorems.Thm_Couret_STROBO2TORS_recoh_stability_cubic_reading_norm
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_probe_is_sign
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

/-- A binary character trivial on the ternary direction has amplitude
exactly one or three on the exceptional representative. -/
theorem recoh_binary_param_probe_norm (chi : AddChar G ℂ) (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) (hcv : chi v = 1) :
    ‖recohSupportProbe chi (paramSupport ((a, d), v))‖ = 1 ∨
      ‖recohSupportProbe chi (paramSupport ((a, d), v))‖ = 3 := by
  rw [recoh_param_probe_formula chi a d v hd hd0 hv hv0, hcv]
  rcases recoh_two_torsion_probe_is_sign chi chi.map_add_eq_mul chi.map_zero_eq_one
    d hd with hpos | hneg
  · right
    rw [hpos, norm_mul, recoh_finite_character_norm_one]
    norm_num
  · left
    rw [hneg, norm_mul, recoh_finite_character_norm_one]
    norm_num

theorem recoh_binary_param_probe_norm_ge_one (chi : AddChar G ℂ) (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) (hcv : chi v = 1) :
    1 ≤ ‖recohSupportProbe chi (paramSupport ((a, d), v))‖ := by
  rcases recoh_binary_param_probe_norm chi a d v hd hd0 hv hv0 hcv with h | h
  · rw [h]
  · rw [h]; norm_num

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









/-- The canonical kind of exceptional bank attains separation two:
binary slots detect all involutions and kill the ternary direction,
while one ternary slot detects that direction and kills involutions. -/
theorem p2m_local_recoh_param_probe_separated_two
    {I : Type*} (bank : I → AddChar G ℂ) (chi : AddChar G ℂ)
    (a d v : G) (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0)
    (hbinary : ∀ i, bank i v = 1)
    (hsep : ∀ u : G, u + u = 0 → (∀ i, bank i u = 1) → u = 0)
    (htrivial : ∀ u : G, u + u = 0 → chi u = 1) (hdetect : chi v ≠ 1) :
    RecohProbeSeparated (Sum.elim bank (fun _ : Unit => chi))
      (squareFibre (paramSupport ((a, d), v))) 2 := by
  have hp := recoh_probe_separated_torsion_orbit bank (paramSupport ((a, d), v)) 1
    (fun i => recoh_binary_param_probe_norm_ge_one (bank i) a d v hd hd0 hv hv0 (hbinary i)) hsep
  have hnv : ∀ i, bank i (-v) = 1 := by
    intro i
    have h := ((bank i).map_add_eq_mul v (-v)).symm
    simpa [hbinary i] using h
  have hn := recoh_probe_separated_torsion_orbit bank (paramSupport ((a, d), -v)) 1
    (fun i => recoh_binary_param_probe_norm_ge_one (bank i) a d (-v) hd hd0
      (three_torsion_neg v hv) (neg_ne_zero.mpr hv0) (hnv i)) hsep
  rw [recoh_param_square_fibre_eq a d v hd hd0 hv hv0]
  apply recoh_probe_separated_two_orbits bank chi _ _ 2
    (by simpa using hp) (by simpa using hn) htrivial
  have hdist := recoh_ternary_param_probe_distance chi a d v 0 hd hd0 hv hv0
    (htrivial d hd) chi.map_zero_eq_one hdetect
  have hdist' : ‖recohSupportProbe chi (paramSupport ((a, d), v)) -
      recohSupportProbe chi (paramSupport ((a, d), -v))‖ = 2 * Real.sqrt 3 := by
    simpa [translateSupport] using hdist
  rw [hdist']
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

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
                  (bank i) v)
                (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
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
                @Ne.{1} Complex
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
                      chi v)
                    (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
                  @Couret.STROBO2TORS.RecohProbeSeparated.{p2m_u_0, p2m_u_1} G inst (Sum.{p2m_u_1, 0} I Unit)
                    (@Sum.elim.{p2m_u_1, 0, p2m_u_0 + 1} I Unit
                      (@AddChar.{p2m_u_0, 0} G
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                      bank fun x => chi)
                    (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2
                      (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                        (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
                          (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v)))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_param_probe_separated_two

