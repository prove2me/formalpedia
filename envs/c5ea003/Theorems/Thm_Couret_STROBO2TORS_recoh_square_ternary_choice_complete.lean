-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_square_ternary_choice_complete
-- name    : Couret.STROBO2TORS.recoh_square_ternary_choice_complete
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:54.956962+00:00
-- url     : https://prove2.me/theorems/5fff2135-c610-4d84-951a-fe0fb1d21c62
-- title:
--   A realized square supplies one orbit or a passing ternary coordinate
-- statement:
--   Let $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$ for positive natural moduli $q_j$. Let $E$ be sparse square entries realized by a three-element support $S$. Let $D$ be the specified cyclic square representatives. Then
--
--   $$\operatorname{OneOrbitCheck}(D)=\mathrm{true}\quad\lor\quad\exists j,\operatorname{Select}(q,E)=\operatorname{some}(j)\land\operatorname{TernaryOrbitCheck}(D,j)=\mathrm{true}.$$
--
--   The ternary orbit check requires equal coordinate readings to imply that two representatives are two-torsion translates.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSquareSelector.lean, lines 328–361; source file SHA-256 a8eaaafaf12bee0781361925c6726f9d658ee4df71e8e3c8436c68366ccc7438; theorem Couret.STROBO2TORS.recoh_square_ternary_choice_complete

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_fibre_orbit_separator
import Theorems.Thm_Couret_STROBO2TORS_recoh_first_passing_exists
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

theorem recoh_square_ternary_choice_complete
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hsquare : orderedSquare S = recohTypedSquareValue entries) :
    recohOneOrbitCheck (recohCyclicSquareRepresentatives q entries) = true ∨
      ∃ j, recohSquareTernaryChoice q entries = some j ∧
        recohTernaryOrbitCheck q (recohCyclicSquareRepresentatives q entries) j = true := by sorry






end Cyclic

end Couret.STROBO2TORS
