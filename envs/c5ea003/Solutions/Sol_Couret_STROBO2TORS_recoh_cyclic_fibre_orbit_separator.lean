-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_fibre_orbit_separator
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:00:43.99763+00:00
-- url     : https://prove2.me/submissions/57fe6bb5-78f0-4d39-9cf2-1fc11e964341

import Aesop
import Definitions.Def_Couret_RecohTernaryFibreSelector_4c0db0f29983
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
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_param_fibre_selected_separator
import Theorems.Thm_Couret_STROBO2TORS_recoh_exceptional_normal_form
import Theorems.Thm_Couret_STROBO2TORS_recoh_ordinary_partner_of_common_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_two_h_iff_exception
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
import Definitions.Def_Couret_RecohTernarySelector_13a2b1134dfc
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883

set_option autoImplicit false

/-!
A single concrete ternary coordinate separates the two translation orbits
of any exceptional triple fibre in a product of cyclic groups. The witness
comes from the executable direction selector. The conclusion quantifies over
the entire fibre, so the later square-only search may use any complete set
of orbit representatives rather than knowing the hidden support.
-/

namespace Couret.STROBO2TORS



variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





/-- All representatives of an ordinary fibre belong to one torsion orbit;
an exceptional fibre has a common separating coordinate for all its pairs. -/
theorem p2m_local_recoh_cyclic_fibre_orbit_separator
    (data3 : RecohPrimaryFactorData q 3)
    (S : Finset ((j : Fin d) → ZMod (q j))) (hS : S.card = 3) :
    (∀ B ∈ squareFibre S, ∀ C ∈ squareFibre S, OrdinaryPartner B C) ∨
      ∃ i : RecohPrimaryCoordinate q 3,
        ∀ B ∈ squareFibre S, ∀ C ∈ squareFibre S,
          recohSupportProbe (recohCyclicPrimaryBank q 3 data3 i) B =
            recohSupportProbe (recohCyclicPrimaryBank q 3 data3 i) C →
          OrdinaryPartner B C := by
  rcases squareFibre_card_h_or_two_h S hS with ho | he
  · left
    have hfibre : squareFibre S = torsionOrbit S := by
      apply (Finset.eq_of_subset_of_card_le (torsionOrbit_subset_fibre S hS) ?_).symm
      rw [ho, torsionOrbit_card S hS]
    intro B hB C hC
    rw [hfibre] at hB hC
    exact recoh_ordinary_partner_of_common_torsion_orbit S B C hB hC
  · right
    obtain ⟨T, hT⟩ := (squareFibre_card_two_h_iff_exception S hS).mp he
    obtain ⟨a, t, v, u, ht, ht0, hv, hv0, hu, hs, hT⟩ :=
      recoh_exceptional_normal_form S T hT
    have hvn : 3 • v = 0 := by
      simpa only [succ_nsmul, zero_nsmul, zero_add] using hv
    refine ⟨recohTernaryCoordinate q v hvn hv0, ?_⟩
    rw [hs]
    intro B hB C hC heq
    exact recoh_cyclic_param_fibre_selected_separator q data3 a t v
      ht ht0 hv hv0 hvn B C hB hC heq

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (data3 : @Couret.STROBO2TORS.RecohPrimaryFactorData d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (S : Finset.{0} ((j : Fin d) → ZMod (q j))),
  @Eq.{1} Nat (@Finset.card.{0} ((j : Fin d) → ZMod (q j)) S)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    Or
      (∀ (B : Finset.{0} ((j : Fin d) → ZMod (q j))),
        @Membership.mem.{0, 0} (Finset.{0} ((j : Fin d) → ZMod (q j)))
            (Finset.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))))
              (Finset.{0} ((j : Fin d) → ZMod (q j))) (@Finset.instSetLike.{0} (Finset.{0} ((j : Fin d) → ZMod (q j)))))
            (@Couret.STROBO2TORS.squareFibre.{0} ((j : Fin d) → ZMod (q j))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              (@Pi.instFintype.{0, 0} (Fin d) (fun j => ZMod (q j)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
                @ZMod.fintype (q a) (inst a))
              S)
            B →
          ∀ (C : Finset.{0} ((j : Fin d) → ZMod (q j))),
            @Membership.mem.{0, 0} (Finset.{0} ((j : Fin d) → ZMod (q j)))
                (Finset.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))))
                  (Finset.{0} ((j : Fin d) → ZMod (q j)))
                  (@Finset.instSetLike.{0} (Finset.{0} ((j : Fin d) → ZMod (q j)))))
                (@Couret.STROBO2TORS.squareFibre.{0} ((j : Fin d) → ZMod (q j))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (fun a b =>
                    @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                      (Fin.fintype d) a b)
                  (@Pi.instFintype.{0, 0} (Fin d) (fun j => ZMod (q j)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
                    @ZMod.fintype (q a) (inst a))
                  S)
                C →
              @Couret.STROBO2TORS.OrdinaryPartner.{0} ((j : Fin d) → ZMod (q j))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                (fun a b =>
                  @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                    (Fin.fintype d) a b)
                B C)
      (@Exists.{1}
        (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        fun i =>
        ∀ (B : Finset.{0} ((j : Fin d) → ZMod (q j))),
          @Membership.mem.{0, 0} (Finset.{0} ((j : Fin d) → ZMod (q j)))
              (Finset.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))))
                (Finset.{0} ((j : Fin d) → ZMod (q j)))
                (@Finset.instSetLike.{0} (Finset.{0} ((j : Fin d) → ZMod (q j)))))
              (@Couret.STROBO2TORS.squareFibre.{0} ((j : Fin d) → ZMod (q j))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                (fun a b =>
                  @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                    (Fin.fintype d) a b)
                (@Pi.instFintype.{0, 0} (Fin d) (fun j => ZMod (q j)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
                  @ZMod.fintype (q a) (inst a))
                S)
              B →
            ∀ (C : Finset.{0} ((j : Fin d) → ZMod (q j))),
              @Membership.mem.{0, 0} (Finset.{0} ((j : Fin d) → ZMod (q j)))
                  (Finset.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))))
                    (Finset.{0} ((j : Fin d) → ZMod (q j)))
                    (@Finset.instSetLike.{0} (Finset.{0} ((j : Fin d) → ZMod (q j)))))
                  (@Couret.STROBO2TORS.squareFibre.{0} ((j : Fin d) → ZMod (q j))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (fun a b =>
                      @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                        (Fin.fintype d) a b)
                    (@Pi.instFintype.{0, 0} (Fin d) (fun j => ZMod (q j)) (instDecidableEqFin d) (Fin.fintype d)
                      fun a => @ZMod.fintype (q a) (inst a))
                    S)
                  C →
                @Eq.{1} Complex
                    (@Couret.STROBO2TORS.recohSupportProbe.{0} ((j : Fin d) → ZMod (q j))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                      (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three data3 i)
                      B)
                    (@Couret.STROBO2TORS.recohSupportProbe.{0} ((j : Fin d) → ZMod (q j))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                      (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three data3 i)
                      C) →
                  @Couret.STROBO2TORS.OrdinaryPartner.{0} ((j : Fin d) → ZMod (q j))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (fun a b =>
                      @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                        (Fin.fintype d) a b)
                    B C) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_fibre_orbit_separator

