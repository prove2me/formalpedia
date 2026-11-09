-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_ternary_candidate_terms_le_six
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:44.742761+00:00
-- url     : https://prove2.me/submissions/03dbc12f-c73b-49f4-b140-ff5be84c9fcf

import Aesop
import Definitions.Def_Couret_RecohCyclicCoefficientDecoder_9d7602a6d6c9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_bank_encoding_length
import Theorems.Thm_Couret_STROBO2TORS_recoh_reduced_terms_length_le
import Definitions.Def_Couret_RecohCyclicCoefficientDecoder_9d7602a6d6c9

set_option autoImplicit false

/-!
The bank actually indexed by the typed cyclic decoder attains the minimal
measurement budget, including its empty bank on odd-order products.
The short-term bounds below apply to candidate triples. No length bound
is imposed on arbitrary externally supplied coefficient observations.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]













omit [∀ i, NeZero (q i)] in
theorem p2m_local_recoh_cyclic_ternary_candidate_terms_le_six
    (i : RecohActiveTernaryCoordinate q)
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (k : ℕ) :
    (recohReducedTerms 3 k (recohCyclicBankEncoding q (Sum.inr i) S)).length ≤ 6 := by
  have h := recoh_reduced_terms_length_le Nat.prime_three k
    (recohCyclicBankEncoding q (Sum.inr i) S)
  simpa only [recoh_cyclic_bank_encoding_length, hS, Nat.reduceSub,
    Nat.reduceMul] using h

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) (i : @Couret.STROBO2TORS.RecohActiveTernaryCoordinate d q)
  (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat
        (@List.length.{0} (Prod.{0, 0} Nat Int)
          (Couret.STROBO2TORS.recohReducedTerms (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k
            (@Couret.STROBO2TORS.recohCyclicBankEncoding d q
              (@Sum.inr.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
                (@Couret.STROBO2TORS.RecohActiveTernaryCoordinate d q) i)
              S)))
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_ternary_candidate_terms_le_six

