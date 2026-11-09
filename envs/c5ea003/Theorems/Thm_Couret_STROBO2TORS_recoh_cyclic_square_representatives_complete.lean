-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_square_representatives_complete
-- name    : Couret.STROBO2TORS.recoh_cyclic_square_representatives_complete
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:51.113582+00:00
-- url     : https://prove2.me/theorems/559c0b80-7da4-4f60-97d5-d14a58455f04
-- title:
--   Every cyclic triple has a square-derived orbit representative
-- statement:
--   Let d be a natural number, let q:Fin d→ℕ have q(i)≠0 for every i, and put H=∏_(i:Fin d) ZMod(q(i)). Let entries be any list of pairs (x,m) with x∈H and m∈ℕ, interpreted as the function R(z) that sums the multiplicities of all list entries located at z. If a finite support S⊆H has cardinality three and its ordered convolution square equals R as a function, then there exists B in recohCyclicSquareRepresentatives(q,entries) such that OrdinaryPartner(B,S): some u∈H satisfies u+u=0 and S=B+u. No separate format check, distinct-location condition on the entries, lower bound q(i)≥2, or zero-free condition is assumed. Dimensions and moduli are allowed to be degenerate; if H has fewer than three elements, the cardinality premise cannot hold.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSquareSelector.lean, lines 300–306; source file SHA-256 a8eaaafaf12bee0781361925c6726f9d658ee4df71e8e3c8436c68366ccc7438; theorem Couret.STROBO2TORS.recoh_cyclic_square_representatives_complete

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

theorem recoh_cyclic_square_representatives_complete
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hsquare : orderedSquare S = recohTypedSquareValue entries) :
    ∃ B ∈ recohCyclicSquareRepresentatives q entries, OrdinaryPartner B S := by sorry












end Cyclic

end Couret.STROBO2TORS
