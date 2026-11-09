-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_square_representatives_card_le_twenty
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:39.324512+00:00
-- url     : https://prove2.me/submissions/fa8fbaa6-e2a2-423c-9467-53e8f1b55c29

import Aesop
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_edge_sets_card_le_twenty
import Theorems.Thm_Couret_STROBO2TORS_recoh_typed_square_support_card_le_six
import Definitions.Def_Couret_RecohCyclicPreparedDecoder_0ae8cdf0a932
import Definitions.Def_Couret_RecohTernaryFibreSelector_4c0db0f29983

set_option autoImplicit false

/-!
Selection from the labelled ordered square using at most twenty explicit
representatives. All runtime checks use finite supports, cyclic coordinates
and integer cyclotomic coefficients. No ambient-group search occurs.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















theorem recoh_square_representatives_card_le_twenty
    (U : Finset G) (R : G → ℕ) (half : G → Option G) (hU : U.card ≤ 6) :
    (recohSquareRepresentatives U R half).card ≤ 20 := by
  exact Finset.card_image_le.trans
    (recoh_prepared_edge_sets_card_le_twenty U half _ hU)







variable [Fintype G]



section FiniteSelection

variable {α : Type*}







end FiniteSelection

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]



























omit [∀ i, NeZero (q i)] in
theorem p2m_local_recoh_cyclic_square_representatives_card_le_twenty
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (hformat : RecohTypedSquareFormat entries) :
    (recohCyclicSquareRepresentatives q entries).card ≤ 20 :=
  recoh_square_representatives_card_le_twenty _ _ _
    ((Finset.card_filter_le _ _).trans
      (recoh_typed_square_support_card_le_six entries hformat))









end Cyclic

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)),
  @Couret.STROBO2TORS.RecohTypedSquareFormat.{0} ((i : Fin d) → ZMod (q i)) entries →
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
        (@Couret.STROBO2TORS.recohCyclicSquareRepresentatives d q entries))
      (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_square_representatives_card_le_twenty

