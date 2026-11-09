-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_selected_observation_injective_on_square
-- name    : Couret.STROBO2TORS.recoh_selected_observation_injective_on_square
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:18:21.314278+00:00
-- url     : https://prove2.me/theorems/9057036a-3c70-48ea-8d2d-028e627bd1ee
-- title:
--   Selected observations reconstruct within the represented square fibre
-- statement:
--   Let $d\in\mathbb N$, let $q_0,\ldots,q_{d-1}$ be positive integers, and put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. Let $S,T$ be three-element supports both having the square function represented by given entries. If their selected-bank observations agree, then
--
--   $$S=T.$$
--
--   This needs no format hypothesis on the entries beyond the two square equalities.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSelectedDecoder.lean, lines 155–176; source file SHA-256 9df6959d546259a3037e3c1d20bf5d4697a947811925e34ec7c4b4ec93c577b0; theorem Couret.STROBO2TORS.recoh_selected_observation_injective_on_square

import Aesop
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_bank_injective_on_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_binary_probe_nonzero
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_bank_separates
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_selected_orbits
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
import Definitions.Def_Couret_RecohFibreOptimal_b9d6825ce497

set_option autoImplicit false

/-!
The typed coefficient decoder with all binary coordinates and at most one
ternary coordinate selected from the labelled square. The square selector
runs before observed character coefficients are supplied. Its exact integer
backend retains the previously certified half-sum and sign-recovery code.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_selected_observation_injective_on_square
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S T : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3) (hT : T.card = 3)
    (hSR : orderedSquare S = recohTypedSquareValue entries)
    (hTR : orderedSquare T = recohTypedSquareValue entries)
    (hobs : recohObservation (recohSelectedObservedBank q entries) S =
      recohObservation (recohSelectedObservedBank q entries) T) : S = T := by sorry






























end Couret.STROBO2TORS
