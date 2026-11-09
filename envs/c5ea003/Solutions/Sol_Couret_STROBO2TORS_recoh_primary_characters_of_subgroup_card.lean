-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_primary_characters_of_subgroup_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:07.010236+00:00
-- url     : https://prove2.me/submissions/fa5a9d8f-5808-42e3-9796-283fbfab2214

import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Theorems.Thm_Couret_STROBO2TORS_recoh_complex_character_extension
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality

set_option autoImplicit false

/-!
Primary complex character banks for finite abelian groups.

The construction takes coordinates on the subgroup killed by a prime p,
extends their standard complex characters to G, then raises each extension
to the factor of |G| coprime to p.  This gives p-primary characters without
assuming that G itself has exponent p.  All existence statements below are
proved from group structure and cardinality; separation is a conclusion.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G]







/-- An elementary abelian group of cardinality `p^r` has `r` coordinates
over `ZMod p`; its module structure is constructed from the exponent. -/
theorem recoh_prime_coordinates_of_card
    {H : Type*} [AddCommGroup H] [Fintype H]
    (p r : ℕ) [Fact p.Prime]
    (hpH : ∀ x : H, p • x = 0)
    (hcard : Fintype.card H = p ^ r) :
    Nonempty (H ≃+ (Fin r → ZMod p)) := by
  classical
  letI : Module (ZMod p) H := AddCommGroup.zmodModule (n := p) hpH
  have hdim : Module.finrank (ZMod p) H = r := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    calc
      p ^ Module.finrank (ZMod p) H = Fintype.card H := by
        simpa only [ZMod.card] using
          (Module.card_eq_pow_finrank (K := ZMod p) (V := H)).symm
      _ = p ^ r := hcard
  exact ⟨(Module.finBasisOfFinrankEq (ZMod p) H hdim).equivFun.toAddEquiv⟩

variable [Fintype G]





/-- Raising a character to the prime-to-`p` cofactor of `|G|` makes
every value a root of unity of uniformly bounded `p`-power order. -/
theorem recoh_character_primary_projection_pow
    (p : ℕ) (χ : AddChar G ℂ) (x : G) :
    ((χ ^ (Fintype.card G / p ^ (Fintype.card G).factorization p)) x) ^
      (p ^ (Fintype.card G).factorization p) = 1 := by
  rw [AddChar.pow_apply, ← pow_mul, Nat.mul_comm,
    Nat.ordProj_mul_ordCompl_eq_self]
  rw [← χ.map_nsmul_eq_pow, card_nsmul_eq_zero, χ.map_zero_eq_one]

/-- A bank of `r` primary characters separates an elementary abelian
subgroup of cardinality `p^r`.  The ambient group may have higher
`p`-power torsion and arbitrary other primary factors. -/
theorem p2m_local_recoh_primary_characters_of_subgroup_card
    (p r : ℕ) [Fact p.Prime] (A : AddSubgroup G)
    (hpA : ∀ a : A, p • a = 0)
    (hcard : Nat.card A = p ^ r) :
    ∃ bank : Fin r → AddChar G ℂ,
      (∀ i x, (bank i x) ^ (p ^ (Fintype.card G).factorization p) = 1) ∧
      (∀ a : A, (∀ i, bank i (a : G) = 1) → a = 0) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have hcard' : Fintype.card A = p ^ r := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨e⟩ := recoh_prime_coordinates_of_card p r hpA hcard'
  let coord : Fin r → A →+ ZMod p := fun i =>
    { toFun := fun a => e a i
      map_zero' := by simp
      map_add' := fun a b => by simp }
  let restriction : Fin r → AddChar A ℂ := fun i =>
    ZMod.stdAddChar.compAddMonoidHom (coord i)
  choose χ hχ using fun i : Fin r =>
    recoh_complex_character_extension A (restriction i)
  let q : ℕ := Fintype.card G / p ^ (Fintype.card G).factorization p
  let bank : Fin r → AddChar G ℂ := fun i => χ i ^ q
  refine ⟨bank, ?_, ?_⟩
  · intro i x
    exact recoh_character_primary_projection_pow p (χ i) x
  · intro a ha
    apply e.injective
    funext i
    have hpa : p • (a : G) = 0 := congrArg (fun y : A => (y : G)) (hpA a)
    have hχp : (χ i (a : G)) ^ p = 1 := by
      rw [← (χ i).map_nsmul_eq_pow, hpa, (χ i).map_zero_eq_one]
    have hχq : (χ i (a : G)) ^ q = 1 := by
      exact ha i
    have hχone : χ i (a : G) = 1 :=
      recoh_eq_one_of_coprime_powers _ p q
        (Nat.coprime_ordCompl (Fact.out : p.Prime) Fintype.card_ne_zero)
        hχp hχq
    have hstd : ZMod.stdAddChar (e a i) = 1 := (hχ i a).symm.trans hχone
    have hcoord : e a i = 0 := ZMod.injective_stdAddChar
      (hstd.trans (ZMod.stdAddChar (N := p)).map_zero_eq_one.symm)
    simpa only [map_zero, Pi.zero_apply] using hcoord









end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : Fintype.{p2m_u_0} G] (p r : Nat) [Fact (Nat.Prime p)]
  (A : @AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)),
  (∀
      (a :
        @Subtype.{p2m_u_0 + 1} G fun x =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            A x),
      @Eq.{p2m_u_0 + 1}
        (@Subtype.{p2m_u_0 + 1} G fun x =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            A x)
        (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat
          (@Subtype.{p2m_u_0 + 1} G fun x =>
            @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
              A x)
          (@Subtype.{p2m_u_0 + 1} G fun x =>
            @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
              A x)
          (@instHSMul.{0, p2m_u_0} Nat
            (@Subtype.{p2m_u_0 + 1} G fun x =>
              @Membership.mem.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                  (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                A x)
            (@AddSubgroup.nsmul.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) A))
          p a)
        (@OfNat.ofNat.{p2m_u_0}
          (@Subtype.{p2m_u_0 + 1} G fun x =>
            @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
              A x)
          (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0}
            (@Subtype.{p2m_u_0 + 1} G fun x =>
              @Membership.mem.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                  (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                A x)
            (@AddSubgroup.zero.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) A)))) →
    @Eq.{1} Nat
        (Nat.card.{p2m_u_0}
          (@Subtype.{p2m_u_0 + 1} G fun x =>
            @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
              A x))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) p r) →
      @Exists.{p2m_u_0 + 1}
        (Fin r →
          @AddChar.{p2m_u_0, 0} G
            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
        fun bank =>
        And
          (∀ (i : Fin r) (x : G),
            @Eq.{1} Complex
              (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                (@instHPow.{0, 0} Complex Nat
                  (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
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
                  (bank i) x)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) p
                  (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                    Nat (fun x => Nat)
                    (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                    (Nat.factorization (@Fintype.card.{p2m_u_0} G inst_1)) p)))
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
          (∀
            (a :
              @Subtype.{p2m_u_0 + 1} G fun x =>
                @Membership.mem.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                    (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  A x),
            (∀ (i : Fin r),
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
                    (bank i)
                    (@Subtype.val.{p2m_u_0 + 1} G
                      (fun x =>
                        @Membership.mem.{p2m_u_0, p2m_u_0} G
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                          A x)
                      a))
                  (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
              @Eq.{p2m_u_0 + 1}
                (@Subtype.{p2m_u_0 + 1} G fun x =>
                  @Membership.mem.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                      (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    A x)
                a
                (@OfNat.ofNat.{p2m_u_0}
                  (@Subtype.{p2m_u_0 + 1} G fun x =>
                    @Membership.mem.{p2m_u_0, p2m_u_0} G
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                        (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      A x)
                  (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0}
                    (@Subtype.{p2m_u_0 + 1} G fun x =>
                      @Membership.mem.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        A x)
                    (@AddSubgroup.zero.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) A)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_primary_characters_of_subgroup_card

