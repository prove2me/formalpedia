-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stable_bank_separated
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:18:56.593196+00:00
-- url     : https://prove2.me/submissions/a9ae0380-2290-4465-884e-616e757938f9

import Aesop
import Definitions.Def_Couret_RecohStableBank_b01db9b053a3
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_bank_separates
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_separated_square_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_selected_orbits
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_probe_is_sign
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8

set_option autoImplicit false

/-!
Quantitative reconstruction with the square-selected minimum-size bank.
Each binary character is replaced by a prescribed odd power; the selected
ternary character and the measurement index type are unchanged.

The multipliers are parameters of the bank and are fixed before readings are
received. The quantitative theorems require a certified amplitude bound on
the square fibre. A separate square-only selector supplies these parameters
and that bound.

The rational-decoder bridges use a supplied candidate set contained in the
fibre. They do not introduce an executable enumeration of the ambient group
or its powerset. Prediction error is included in the uniqueness budget.
-/

namespace Couret.STROBO2TORS

/-- Odd powers leave the restriction of any character to two-torsion
unchanged. -/
theorem recoh_character_odd_power_on_two
    {G : Type*} [AddCommGroup G] (chi : AddChar G ℂ)
    (k : ℕ) (hk : Odd k) (u : G) (hu : u + u = 0) :
    (chi ^ k) u = chi u := by
  classical
  rw [AddChar.pow_apply]
  rcases recoh_two_torsion_probe_is_sign chi chi.map_add_eq_mul
    chi.map_zero_eq_one u hu with h | h
  · simp [h]
  · rw [h, hk.neg_one_pow]

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]









theorem recoh_stable_binary_bank_on_two (multipliers : RecohEvenCoordinate q → ℕ)
    (hodd : ∀ i, Odd (multipliers i)) (i : RecohEvenCoordinate q)
    (u : (j : Fin d) → ZMod (q j)) (hu : u + u = 0) :
    recohStableBinaryBank q multipliers i u =
      recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i u :=
  recoh_character_odd_power_on_two
    (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i)
    (multipliers i) (hodd i) u hu



/-- Preserving the signs preserves detection of every nonzero involution. -/
theorem recoh_stable_binary_bank_separates
    (multipliers : RecohEvenCoordinate q → ℕ) (hodd : ∀ i, Odd (multipliers i))
    (u : (j : Fin d) → ZMod (q j)) (hu : u + u = 0)
    (hbank : ∀ i, recohStableBinaryBank q multipliers i u = 1) : u = 0 := by
  apply recoh_cyclic_primary_bank_separates q 2 (recohCanonicalPrimaryData q 2) u
    (by simpa only [two_nsmul] using hu)
  intro i
  rw [← recoh_stable_binary_bank_on_two q multipliers hodd i u hu]
  exact hbank i







/-- The existing square-only ternary selector and any certified binary
amplitude bound give quantitative separation with the same slots. -/
theorem p2m_local_recoh_stable_bank_separated
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (multipliers : RecohEvenCoordinate q → ℕ) (hodd : ∀ i, Odd (multipliers i))
    (S : Finset ((i : Fin d) → ZMod (q i)))
    (hSR : orderedSquare S = recohTypedSquareValue entries)
    (a : ℝ) (ha : a ≤ Real.sqrt 3)
    (hamp : ∀ T ∈ squareFibre S, ∀ i, a ≤ ‖recohSupportProbe
      (recohStableBinaryBank q multipliers i) T‖) :
    RecohProbeSeparated (recohStableObservedBank q entries multipliers)
      (squareFibre S) (2 * a) := by
  apply recoh_probe_separated_square_fibre
    (recohStableBinaryBank q multipliers)
    (fun i : RecohSelectedTernaryIndex q entries =>
      recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) i.val)
    S a ha hamp
  · exact recoh_stable_binary_bank_separates q multipliers hodd
  · intro j u hu
    exact recoh_cyclic_ternary_bank_trivial_on_two q (recohCanonicalPrimaryData q 3) j.val u hu
  · intro B hB C hC hread
    have hBdata := (mem_squareFibre S B).mp hB
    have hCdata := (mem_squareFibre S C).mp hC
    have hBR : orderedSquare B = recohTypedSquareValue entries := by
      funext z
      exact (hBdata.2 z).symm.trans (congrFun hSR z)
    have hCR : orderedSquare C = recohTypedSquareValue entries := by
      funext z
      exact (hCdata.2 z).symm.trans (congrFun hSR z)
    apply recoh_square_selected_orbits q entries B C hBdata.1 hCdata.1 hBR hCR
    intro j hj
    exact hread ⟨j, hj⟩













end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (multipliers : @Couret.STROBO2TORS.RecohEvenCoordinate d q → Nat),
  (∀ (i : @Couret.STROBO2TORS.RecohEvenCoordinate d q), @Odd.{0} Nat Nat.instSemiring (multipliers i)) →
    ∀ (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
      @Eq.{1} (((i : Fin d) → ZMod (q i)) → Nat)
          (@Couret.STROBO2TORS.orderedSquare.{0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            S)
          (@Couret.STROBO2TORS.recohTypedSquareValue.{0} ((i : Fin d) → ZMod (q i))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            entries) →
        ∀ (a : Real),
          @LE.le.{0} Real Real.instLE a
              (Real.sqrt
                (@OfNat.ofNat.{0} Real (nat_lit 3)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
            (∀ (T : Finset.{0} ((i : Fin d) → ZMod (q i))),
                @Membership.mem.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
                    (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                      (Finset.{0} ((i : Fin d) → ZMod (q i)))
                      (@Finset.instSetLike.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))))
                    (@Couret.STROBO2TORS.squareFibre.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                      (fun a b =>
                        @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a))
                          (fun a => ZMod.decidableEq (q a)) (Fin.fintype d) a b)
                      (@Pi.instFintype.{0, 0} (Fin d) (fun i => ZMod (q i)) (instDecidableEqFin d) (Fin.fintype d)
                        fun a => @ZMod.fintype (q a) (inst a))
                      S)
                    T →
                  ∀ (i : @Couret.STROBO2TORS.RecohEvenCoordinate d q),
                    @LE.le.{0} Real Real.instLE a
                      (@Norm.norm.{0} Complex Complex.instNorm
                        (@Couret.STROBO2TORS.recohSupportProbe.{0} ((i : Fin d) → ZMod (q i))
                          (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                            @Ring.toAddCommGroup.{0} (ZMod (q i))
                              (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                          (@Couret.STROBO2TORS.recohStableBinaryBank d q inst multipliers i) T))) →
              @Couret.STROBO2TORS.RecohProbeSeparated.{0, 0} ((i : Fin d) → ZMod (q i))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                (@Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries)
                (@Couret.STROBO2TORS.recohStableObservedBank d q inst entries multipliers)
                (@Couret.STROBO2TORS.squareFibre.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (fun a b =>
                    @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                      (Fin.fintype d) a b)
                  (@Pi.instFintype.{0, 0} (Fin d) (fun i => ZMod (q i)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
                    @ZMod.fintype (q a) (inst a))
                  S)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  a) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stable_bank_separated

