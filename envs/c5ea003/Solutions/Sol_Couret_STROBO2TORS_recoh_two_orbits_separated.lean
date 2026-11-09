-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_two_orbits_separated
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:24.095939+00:00
-- url     : https://prove2.me/submissions/b03a30d5-fa84-436c-9710-a45b784b1c8b

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_orbit_translation_separated
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

/-!
RECOH conditional reconstruction, step 1: orbit separation.
This is an abstract lemma requiring nonvanishing covariant probes and
characters separating two-torsion. No unproved character-existence
assumption is hidden in this theorem.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]





/-- In the aligned-signature case, one additional covariant measurement
that separates the two representatives separates their whole orbits.
Character existence is intentionally not asserted by this lemma. -/
theorem p2m_local_recoh_two_orbits_separated
    {I : Type*} (bank : I → AddChar G ℂ)
    (beta : AddChar G ℂ) (S T : Finset G)
    (probe : I → Finset G → ℂ) (extra : Finset G → ℂ)
    (hcovS : ∀ i u, probe i (translateSupport S u) = bank i u * probe i S)
    (hcovT : ∀ i u, probe i (translateSupport T u) = bank i u * probe i T)
    (hextraS : ∀ u, extra (translateSupport S u) = beta u * extra S)
    (hextraT : ∀ u, extra (translateSupport T u) = beta u * extra T)
    (hnonzero : ∀ i, probe i S ≠ 0)
    (hsep : ∀ d : G, d + d = 0 →
      (∀ i, bank i d = 1) → d = 0)
    (hbase : ∀ i, probe i S = probe i T)
    (hbeta : extra S ≠ extra T)
    (u v : G) (hu : u + u = 0) (hv : v + v = 0)
    (hmatch : ∀ i, probe i (translateSupport S u) =
      probe i (translateSupport T v))
    (hbetaMatch : extra (translateSupport S u) =
      extra (translateSupport T v)) : False := by
  have hsame : ∀ i, probe i (translateSupport S u) =
      probe i (translateSupport S v) := by
    intro i
    calc
      probe i (translateSupport S u) =
          probe i (translateSupport T v) := hmatch i
      _ = bank i v * probe i T := hcovT i v
      _ = bank i v * probe i S := by rw [← hbase i]
      _ = probe i (translateSupport S v) := (hcovS i v).symm
  have huv : u = v :=
    recoh_orbit_translation_separated bank S probe hcovS hnonzero hsep
      u v hu hv hsame
  subst v
  rw [hextraS, hextraT] at hbetaMatch
  have hnonzeroBeta : beta u ≠ 0 := by
    intro hz
    have hh := beta.map_add_eq_mul u (-u)
    simp [hz] at hh
  exact hbeta (mul_left_cancel₀ hnonzeroBeta hbetaMatch)


end Couret.STROBO2TORS

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {I : Type p2m_u_1}
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (beta :
    @AddChar.{p2m_u_0, 0} G
      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (S T : Finset.{p2m_u_0} G) (probe : I → Finset.{p2m_u_0} G → Complex) (extra : Finset.{p2m_u_0} G → Complex),
  (∀ (i : I) (u : G),
      @Eq.{1} Complex (probe i (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S u))
        (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
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
          (probe i S))) →
    (∀ (i : I) (u : G),
        @Eq.{1} Complex (probe i (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 T u))
          (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
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
            (probe i T))) →
      (∀ (u : G),
          @Eq.{1} Complex (extra (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S u))
            (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
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
                beta u)
              (extra S))) →
        (∀ (u : G),
            @Eq.{1} Complex (extra (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 T u))
              (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
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
                  beta u)
                (extra T))) →
          (∀ (i : I),
              @Ne.{1} Complex (probe i S)
                (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero))) →
            (∀ (d : G),
                @Eq.{p2m_u_0 + 1} G
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      d d)
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
                          (bank i) d)
                        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
                    @Eq.{p2m_u_0 + 1} G d
                      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                        (@Zero.toOfNat0.{p2m_u_0} G
                          (@NegZeroClass.toZero.{p2m_u_0} G
                            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))) →
              (∀ (i : I), @Eq.{1} Complex (probe i S) (probe i T)) →
                @Ne.{1} Complex (extra S) (extra T) →
                  ∀ (u v : G),
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
                      @Eq.{p2m_u_0 + 1} G
                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            v v)
                          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                            (@Zero.toOfNat0.{p2m_u_0} G
                              (@NegZeroClass.toZero.{p2m_u_0} G
                                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
                        (∀ (i : I),
                            @Eq.{1} Complex (probe i (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S u))
                              (probe i (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 T v))) →
                          @Eq.{1} Complex (extra (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S u))
                              (extra (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 T v)) →
                            False := @_root_.Couret.STROBO2TORS.p2m_local_recoh_two_orbits_separated

