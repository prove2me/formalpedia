-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_square_representatives_card_le_twenty
-- name    : Couret.STROBO2TORS.recoh_cyclic_square_representatives_card_le_twenty
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:33.475263+00:00
-- url     : https://prove2.me/theorems/26cdfb7d-3175-417c-a8f0-885865a0b2fa
-- title:
--   Typed cyclic square inputs yield at most twenty representatives
-- statement:
--   Let d be any natural number and q : Fin d → ℕ be arbitrary, allowing q(i)=0. Put G = product over i in Fin d of ZMod(q(i)). Let entries be a list of pairs in G × ℕ satisfying RecohTypedSquareFormat: its length is between three and six, its positions are pairwise distinct, each count is between one and three, the total count is nine, and the sum of the count residues modulo two is either one or three. Then the finite set recohCyclicSquareRepresentatives q entries has cardinality at most twenty. The construction retains the positions with nonzero interpreted count, takes feasible three-element edge subsets, chooses halves using recohProductHalf q, checks each decoded support against the typed square, and forms the finite-set image of the surviving representatives. The claim requires no nonzero-modulus instance and includes d=0 and inputs not realizable as any triple square; the resulting representative set may be empty.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSquareSelector.lean, lines 308–315; source file SHA-256 a8eaaafaf12bee0781361925c6726f9d658ee4df71e8e3c8436c68366ccc7438; theorem Couret.STROBO2TORS.recoh_cyclic_square_representatives_card_le_twenty

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























variable [Fintype G]



section FiniteSelection

variable {α : Type*}







end FiniteSelection

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

omit [∀ i, NeZero (q i)] in
theorem recoh_cyclic_square_representatives_card_le_twenty
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (hformat : RecohTypedSquareFormat entries) :
    (recohCyclicSquareRepresentatives q entries).card ≤ 20 := by sorry










end Cyclic

end Couret.STROBO2TORS
