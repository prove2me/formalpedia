-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_mem_selected_coefficient_decoder_iff
-- name    : Couret.STROBO2TORS.recoh_mem_selected_coefficient_decoder_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:18:40.343254+00:00
-- url     : https://prove2.me/theorems/9ac96269-80ad-48e0-a959-a6120e3fbaec
-- title:
--   Selected decoder membership includes input validation
-- statement:
--   Let $d\in\mathbb N$, let $q_0,\ldots,q_{d-1}$ be positive integers, and put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. Use the square-selected bank consisting of all even-coordinate two-primary characters and at most one selected ternary character. For arbitrary typed square entries and selected-bank sparse terms, a support $S$ is in the selected coefficient decoder exactly when
--
--   $$\mathrm{Format}(\mathrm{entries},T),\qquad |S|=3,\qquad\operatorname{Obs}_{\rm selected}(S)=\operatorname{TypedObs}(\mathrm{entries},T).$$
--
--   The format is: The input has $q_j\ge2$ and $|G|\ge3$. Its square-entry list has between three and six distinct points, multiplicities in $\{1,2,3\}$ totaling nine, and either one or three odd multiplicities. Each coefficient list has distinct exponents, nonzero integer coefficients, and exponents below $(p-1)p^k$ for its primary root of order $p^{k+1}$. This makes rejection of malformed input part of the exact membership criterion.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSelectedDecoder.lean, lines 287–302; source file SHA-256 9df6959d546259a3037e3c1d20bf5d4697a947811925e34ec7c4b4ec93c577b0; theorem Couret.STROBO2TORS.recoh_mem_selected_coefficient_decoder_iff

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_all_coefficient_formats_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_coefficient_core_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_typed_square_format_check_iff
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

theorem recoh_mem_selected_coefficient_decoder_iff
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms)
    (S : Finset ((i : Fin d) → ZMod (q i))) :
    S ∈ recohSelectedCoefficientDecoder q entries terms ↔
      RecohSelectedInputFormat q entries terms ∧ S.card = 3 ∧
        recohObservation (recohSelectedObservedBank q entries) S =
          recohSelectedTypedObservation q entries terms := by sorry








end Couret.STROBO2TORS
