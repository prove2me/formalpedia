-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_parity_representatives_card_le_six
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:30.748842+00:00
-- url     : https://prove2.me/submissions/bdb4480c-dc87-4b06-8c96-c05be06f1440

import Aesop
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_representatives_card_le_six
import Definitions.Def_Couret_RecohParityGenerator_deb90a4bb68d
import Definitions.Def_Couret_RecohCompactOrbitBridge_59017063a1ce

set_option autoImplicit false

/-!
Composition of the parity generator with the historical orbit construction.

The equality below is an equality of finite families of entire H-orbits,
not equality of representatives or their iteration order. Deduplication is
applied to an explicit list enumeration of the parity representatives. The
list and its anchors are inputs with stated representation contracts; no
classical `Finset.toList` is hidden in an executable definition.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]







section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





omit [∀ i, NeZero (q i)] in
theorem p2m_local_recoh_cyclic_parity_representatives_card_le_six
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    (recohCyclicParityRepresentatives q entries).card ≤ 6 := by
  exact recoh_parity_representatives_card_le_six
    (recohSelectedSquareSupport q entries) (recohTypedSquareValue entries)
    (recohProductHalf q)



end Cyclic

end Couret.STROBO2TORS

theorem solution : ∀ {d : Nat} (q : Fin d → Nat) (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
      (@Couret.STROBO2TORS.recohCyclicParityRepresentatives d q entries))
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_parity_representatives_card_le_six

