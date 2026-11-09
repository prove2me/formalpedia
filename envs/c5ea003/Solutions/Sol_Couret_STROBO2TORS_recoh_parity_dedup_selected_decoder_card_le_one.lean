-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_dedup_selected_decoder_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:08.413608+00:00
-- url     : https://prove2.me/submissions/4502cf2c-2185-4de3-b573-6b1aaf455902

import Aesop
import Definitions.Def_Couret_RecohParityDedupTransport_fd9d6ec554ae
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_selected_core_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_coefficient_core_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_coefficient_decoder_card_le_one
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_input_check_iff
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06

set_option autoImplicit false

/-!
Transport through the explicit anchored deduplication model.

An enumeration and an anchor remain explicit inputs with representation
contracts. The decoder really recovers from the retained representatives.
The fibre classification bounds their number by two, without assuming that
the supplied square data are realizable. No Python list-order or JSON
equivalence is claimed by this module.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G I : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]











section CyclicSelected

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]











/-- After the same typed guards, the retained-family decoder returns exactly
the raw parity decoder's outputs, for every typed observation. -/
theorem recoh_parity_dedup_selected_decoder_eq_parity
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (xs : List (Finset ((i : Fin d) → ZMod (q i))))
    (hxs : xs.toFinset = recohCyclicParityRepresentatives q entries)
    (anchor : Finset ((i : Fin d) → ZMod (q i)) → ((i : Fin d) → ZMod (q i)))
    (hanchor : ∀ B ∈ xs, anchor B ∈ B) :
    recohParityDedupSelectedDecoder q entries terms xs anchor =
      recohParitySelectedCoefficientDecoder q entries terms := by
  unfold recohParityDedupSelectedDecoder recohParitySelectedCoefficientDecoder
  split_ifs with hcheck
  · have hf := (recoh_parity_selected_input_check_iff q entries terms).mp hcheck
    rw [recoh_parity_dedup_selected_core_eq_exact q entries terms xs hxs anchor hanchor
      (fun i => (hf.2.2.2 i).1),
      recoh_parity_selected_coefficient_core_eq_exact q entries terms
      (fun i => (hf.2.2.2 i).1)]
  · rfl







theorem p2m_local_recoh_parity_dedup_selected_decoder_card_le_one
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (xs : List (Finset ((i : Fin d) → ZMod (q i))))
    (hxs : xs.toFinset = recohCyclicParityRepresentatives q entries)
    (anchor : Finset ((i : Fin d) → ZMod (q i)) → ((i : Fin d) → ZMod (q i)))
    (hanchor : ∀ B ∈ xs, anchor B ∈ B) :
    (recohParityDedupSelectedDecoder q entries terms xs anchor).card ≤ 1 := by
  rw [recoh_parity_dedup_selected_decoder_eq_parity q entries terms xs hxs anchor hanchor]
  exact recoh_parity_selected_coefficient_decoder_card_le_one q entries terms

end CyclicSelected

end Couret.STROBO2TORS

theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohSparseTerms)
  (xs : List.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))),
  @Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
      (@List.toFinset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
        (fun a b =>
          @Finset.decidableEq.{0} ((i : Fin d) → ZMod (q i))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            a b)
        xs)
      (@Couret.STROBO2TORS.recohCyclicParityRepresentatives d q entries) →
    ∀ (anchor : Finset.{0} ((i : Fin d) → ZMod (q i)) → (i : Fin d) → ZMod (q i)),
      (∀ (B : Finset.{0} ((i : Fin d) → ZMod (q i))),
          @Membership.mem.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
              (List.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
              (@List.instMembership.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))) xs B →
            @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i)) (Finset.{0} ((i : Fin d) → ZMod (q i)))
              (@SetLike.instMembership.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i))) ((i : Fin d) → ZMod (q i))
                (@Finset.instSetLike.{0} ((i : Fin d) → ZMod (q i))))
              B (anchor B)) →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
            (@Couret.STROBO2TORS.recohParityDedupSelectedDecoder d q inst entries terms xs anchor))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_dedup_selected_decoder_card_le_one

