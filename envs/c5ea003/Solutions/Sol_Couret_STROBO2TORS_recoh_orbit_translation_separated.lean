-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_orbit_translation_separated
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:23.621212+00:00
-- url     : https://prove2.me/submissions/579810bf-29b1-44fa-9893-54c373d0b120

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
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

/-- Covariant nonzero character probes distinguish every H-translate.
The actual Fourier probes and a rank-r basis are subsequent obligations. -/
theorem p2m_local_recoh_orbit_translation_separated
    {I : Type*} (bank : I → AddChar G ℂ) (S : Finset G)
    (probe : I → Finset G → ℂ)
    (hcov : ∀ i u, probe i (translateSupport S u) = bank i u * probe i S)
    (hnonzero : ∀ i, probe i S ≠ 0)
    (hsep : ∀ d : G, d + d = 0 →
      (∀ i, bank i d = 1) → d = 0)
    (u v : G) (hu : u + u = 0) (hv : v + v = 0)
    (heq : ∀ i, probe i (translateSupport S u) =
      probe i (translateSupport S v)) : u = v := by
  have heval (i : I) : bank i u = bank i v := by
    have hi := heq i
    rw [hcov i u, hcov i v] at hi
    exact mul_right_cancel₀ (hnonzero i) hi
  have huv : (u + v) + (u + v) = 0 := by
    calc
      (u + v) + (u + v) = (u + u) + (v + v) := by abel
      _ = 0 := by simp [hu, hv]
  have hd : u + v = 0 := by
    apply hsep (u + v) huv
    intro i
    have hv2 : bank i v * bank i v = 1 := by
      have hh := (bank i).map_add_eq_mul v v
      rw [hv] at hh
      simpa using hh.symm
    calc
      bank i (u + v) = bank i u * bank i v :=
        (bank i).map_add_eq_mul u v
      _ = bank i v * bank i v := by rw [heval i]
      _ = 1 := hv2
  calc
    u = -v := eq_neg_of_add_eq_zero_left hd
    _ = v := (eq_neg_of_add_eq_zero_left hv).symm






end Couret.STROBO2TORS

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {I : Type p2m_u_1}
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (S : Finset.{p2m_u_0} G) (probe : I → Finset.{p2m_u_0} G → Complex),
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
                    (probe i (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S v))) →
                @Eq.{p2m_u_0 + 1} G u v := @_root_.Couret.STROBO2TORS.p2m_local_recoh_orbit_translation_separated

