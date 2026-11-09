-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_param_fibre_selected_separator
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:55:47.379836+00:00
-- url     : https://prove2.me/submissions/1d5b843c-d431-4573-97e3-1bd9a30f475a

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_ordinary_partner_of_common_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_recoh_param_square_fibre_eq
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_constant_on_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_recoh_ternary_selected_detects
import Theorems.Thm_Couret_STROBO2TORS_recoh_third_probe_separates_exceptional
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



/-- The coordinate selected for the normal-form direction separates every
pair of distinct two-torsion orbits in that fibre. -/
theorem p2m_local_recoh_cyclic_param_fibre_selected_separator
    (data3 : RecohPrimaryFactorData q 3)
    (a t v : (j : Fin d) → ZMod (q j))
    (ht : t + t = 0) (ht0 : t ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0)
    (hvn : 3 • v = 0)
    (B C : Finset ((j : Fin d) → ZMod (q j)))
    (hB : B ∈ squareFibre (paramSupport ((a, t), v)))
    (hC : C ∈ squareFibre (paramSupport ((a, t), v)))
    (heq :
      recohSupportProbe
        (recohCyclicPrimaryBank q 3 data3 (recohTernaryCoordinate q v hvn hv0)) B =
      recohSupportProbe
        (recohCyclicPrimaryBank q 3 data3 (recohTernaryCoordinate q v hvn hv0)) C) :
    OrdinaryPartner B C := by
  let chi := recohCyclicPrimaryBank q 3 data3 (recohTernaryCoordinate q v hvn hv0)
  have htrivial : ∀ u, u + u = 0 → chi u = 1 :=
    recoh_cyclic_ternary_bank_trivial_on_two q data3 _
  have hdetect : chi v ≠ 1 := recoh_ternary_selected_detects q data3 v hvn hv0
  have hneq : recohSupportProbe chi (paramSupport ((a, t), v)) ≠
      recohSupportProbe chi (paramSupport ((a, t), -v)) := by
    simpa [translateSupport] using
      (recoh_third_probe_separates_exceptional chi a t v 0 ht ht0 hv hv0
        (htrivial t ht) chi.map_zero_eq_one hdetect)
  rw [recoh_param_square_fibre_eq a t v ht ht0 hv hv0] at hB hC
  rcases Finset.mem_union.mp hB with hB | hB
  · rcases Finset.mem_union.mp hC with hC | hC
    · exact recoh_ordinary_partner_of_common_torsion_orbit _ B C hB hC
    · exact (hneq (by
        calc
          recohSupportProbe chi (paramSupport ((a, t), v)) =
              recohSupportProbe chi B :=
            (recoh_probe_constant_on_torsion_orbit chi htrivial _ _ hB).symm
          _ = recohSupportProbe chi C := heq
          _ = recohSupportProbe chi (paramSupport ((a, t), -v)) :=
            recoh_probe_constant_on_torsion_orbit chi htrivial _ _ hC)).elim
  · rcases Finset.mem_union.mp hC with hC | hC
    · exact (hneq (by
        calc
          recohSupportProbe chi (paramSupport ((a, t), v)) =
              recohSupportProbe chi C :=
            (recoh_probe_constant_on_torsion_orbit chi htrivial _ _ hC).symm
          _ = recohSupportProbe chi B := heq.symm
          _ = recohSupportProbe chi (paramSupport ((a, t), -v)) :=
            recoh_probe_constant_on_torsion_orbit chi htrivial _ _ hB)).elim
    · exact recoh_ordinary_partner_of_common_torsion_orbit _ B C hB hC



end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (data3 : @Couret.STROBO2TORS.RecohPrimaryFactorData d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (a t v : (j : Fin d) → ZMod (q j)),
  @Eq.{1} ((j : Fin d) → ZMod (q j))
      (@HAdd.hAdd.{0, 0, 0} ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j))
        (@instHAdd.{0} ((j : Fin d) → ZMod (q j))
          (@Pi.instAdd.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
            @Distrib.toAdd.{0} (ZMod (q i))
              (@instDistribOfSemiring.{0} (ZMod (q i))
                (@CommSemiring.toSemiring.{0} (ZMod (q i))
                  (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
        t t)
      (@OfNat.ofNat.{0} ((j : Fin d) → ZMod (q j)) (nat_lit 0)
        (@Zero.toOfNat0.{0} ((j : Fin d) → ZMod (q j))
          (@Pi.instZero.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
            @MulZeroClass.toZero.{0} (ZMod (q i))
              (@instMulZeroClassOfSemiring.{0} (ZMod (q i))
                (@CommSemiring.toSemiring.{0} (ZMod (q i))
                  (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))) →
    @Ne.{1} ((j : Fin d) → ZMod (q j)) t
        (@OfNat.ofNat.{0} ((j : Fin d) → ZMod (q j)) (nat_lit 0)
          (@Zero.toOfNat0.{0} ((j : Fin d) → ZMod (q j))
            (@Pi.instZero.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
              @MulZeroClass.toZero.{0} (ZMod (q i))
                (@instMulZeroClassOfSemiring.{0} (ZMod (q i))
                  (@CommSemiring.toSemiring.{0} (ZMod (q i))
                    (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))) →
      @Eq.{1} ((j : Fin d) → ZMod (q j))
          (@HAdd.hAdd.{0, 0, 0} ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j))
            (@instHAdd.{0} ((j : Fin d) → ZMod (q j))
              (@Pi.instAdd.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                @Distrib.toAdd.{0} (ZMod (q i))
                  (@instDistribOfSemiring.{0} (ZMod (q i))
                    (@CommSemiring.toSemiring.{0} (ZMod (q i))
                      (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
            (@HAdd.hAdd.{0, 0, 0} ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j))
              (@instHAdd.{0} ((j : Fin d) → ZMod (q j))
                (@Pi.instAdd.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                  @Distrib.toAdd.{0} (ZMod (q i))
                    (@instDistribOfSemiring.{0} (ZMod (q i))
                      (@CommSemiring.toSemiring.{0} (ZMod (q i))
                        (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
              v v)
            v)
          (@OfNat.ofNat.{0} ((j : Fin d) → ZMod (q j)) (nat_lit 0)
            (@Zero.toOfNat0.{0} ((j : Fin d) → ZMod (q j))
              (@Pi.instZero.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                @MulZeroClass.toZero.{0} (ZMod (q i))
                  (@instMulZeroClassOfSemiring.{0} (ZMod (q i))
                    (@CommSemiring.toSemiring.{0} (ZMod (q i))
                      (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))) →
        ∀
          (hv0 :
            @Ne.{1} ((j : Fin d) → ZMod (q j)) v
              (@OfNat.ofNat.{0} ((j : Fin d) → ZMod (q j)) (nat_lit 0)
                (@Zero.toOfNat0.{0} ((j : Fin d) → ZMod (q j))
                  (@Pi.instZero.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                    @MulZeroClass.toZero.{0} (ZMod (q i))
                      (@instMulZeroClassOfSemiring.{0} (ZMod (q i))
                        (@CommSemiring.toSemiring.{0} (ZMod (q i))
                          (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))))
          (hvn :
            @Eq.{1} ((j : Fin d) → ZMod (q j))
              (@HSMul.hSMul.{0, 0, 0} Nat ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j))
                (@instHSMul.{0, 0} Nat ((i : Fin d) → ZMod (q i))
                  (@AddMonoid.toNSMul.{0} ((i : Fin d) → ZMod (q i))
                    (@Pi.addMonoid.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                      @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                          (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                            (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) v)
              (@OfNat.ofNat.{0} ((j : Fin d) → ZMod (q j)) (nat_lit 0)
                (@Zero.toOfNat0.{0} ((j : Fin d) → ZMod (q j))
                  (@Pi.instZero.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                    @MulZeroClass.toZero.{0} (ZMod (q i))
                      (@instMulZeroClassOfSemiring.{0} (ZMod (q i))
                        (@CommSemiring.toSemiring.{0} (ZMod (q i))
                          (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))))
          (B C : Finset.{0} ((j : Fin d) → ZMod (q j))),
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
                (@Couret.STROBO2TORS.paramSupport.{0} ((j : Fin d) → ZMod (q j))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (fun a b =>
                    @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                      (Fin.fintype d) a b)
                  (@Prod.mk.{0, 0} (Prod.{0, 0} ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j)))
                    ((j : Fin d) → ZMod (q j))
                    (@Prod.mk.{0, 0} ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j)) a t) v)))
              B →
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
                  (@Couret.STROBO2TORS.paramSupport.{0} ((j : Fin d) → ZMod (q j))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (fun a b =>
                      @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                        (Fin.fintype d) a b)
                    (@Prod.mk.{0, 0} (Prod.{0, 0} ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j)))
                      ((j : Fin d) → ZMod (q j))
                      (@Prod.mk.{0, 0} ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j)) a t) v)))
                C →
              @Eq.{1} Complex
                  (@Couret.STROBO2TORS.recohSupportProbe.{0} ((j : Fin d) → ZMod (q j))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three data3
                      (@Couret.STROBO2TORS.recohTernaryCoordinate d q inst v hvn hv0))
                    B)
                  (@Couret.STROBO2TORS.recohSupportProbe.{0} ((j : Fin d) → ZMod (q j))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three data3
                      (@Couret.STROBO2TORS.recohTernaryCoordinate d q inst v hvn hv0))
                    C) →
                @Couret.STROBO2TORS.OrdinaryPartner.{0} ((j : Fin d) → ZMod (q j))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (fun a b =>
                    @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                      (Fin.fintype d) a b)
                  B C := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_param_fibre_selected_separator

