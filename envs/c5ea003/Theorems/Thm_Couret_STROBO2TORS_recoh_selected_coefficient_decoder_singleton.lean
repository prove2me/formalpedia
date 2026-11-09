-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_selected_coefficient_decoder_singleton
-- name    : Couret.STROBO2TORS.recoh_selected_coefficient_decoder_singleton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:27.503696+00:00
-- url     : https://prove2.me/theorems/d24309cc-77de-4cd4-bb7d-cdb438260104
-- title:
--   Selected coefficient decoding has one actual solution
-- statement:
--   Let $d\ge0$, let $q_i$ be nonzero natural numbers for $i<d$, and set $A=\prod_{i<d}\mathbb Z/q_i$. A primary coordinate for a prime $p$ is an index with $p\mid q_i$. For supports in $A$, write $Q_S$ for ordered-sum counts, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a character bank $B$. For typed square entries $E$ on $A$ and sparse term lists $L$ in the selected-bank input format, let $S$ have three elements and observation equal to the selected typed observation. Then $$D_{\mathrm{selected}}(E,L)=\{S\}.$$
--
--   This is exact recovery under the explicit format and observation hypotheses.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSelectedDecoder.lean, lines 315–336; source file SHA-256 9df6959d546259a3037e3c1d20bf5d4697a947811925e34ec7c4b4ec93c577b0; theorem Couret.STROBO2TORS.recoh_selected_coefficient_decoder_singleton

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_selected_coefficient_decoder_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_observation_injective_on_square
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

theorem recoh_selected_coefficient_decoder_singleton
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms)
    (hformat : RecohSelectedInputFormat q entries terms)
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hobs : recohObservation (recohSelectedObservedBank q entries) S =
      recohSelectedTypedObservation q entries terms) :
    recohSelectedCoefficientDecoder q entries terms = {S} := by sorry




end Couret.STROBO2TORS
