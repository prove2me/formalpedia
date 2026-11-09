-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_ternary_candidate_terms_le_six
-- name    : Couret.STROBO2TORS.recoh_cyclic_ternary_candidate_terms_le_six
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:43.131122+00:00
-- url     : https://prove2.me/theorems/428c565f-f5fb-45a8-8df9-2437ea63bbbc
-- title:
--   A ternary triple encoding reduces to at most six terms
-- statement:
--   Let $q_j$ be arbitrary natural moduli, let $i$ index an active ternary coordinate of the specified cyclic bank, and let $S\subseteq\prod_{j<d}\mathbb Z/q_j\mathbb Z$ have size three. For any natural depth $k$,
--
--   $$|\operatorname{ReducedTerms}_{3,k}(\operatorname{encode}_i(S))|\le6.$$
--
--   The moduli need not be nonzero for this length bound; repeated terms are counted before canonical combination.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicDecoderOptimal.lean, lines 101–110; source file SHA-256 b9a6a9f00591eaed0b13b93930156abd42380859ca93bd38dd62091f8d615fb4; theorem Couret.STROBO2TORS.recoh_cyclic_ternary_candidate_terms_le_six

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
theorem recoh_cyclic_ternary_candidate_terms_le_six
    (i : RecohActiveTernaryCoordinate q)
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (k : ℕ) :
    (recohReducedTerms 3 k (recohCyclicBankEncoding q (Sum.inr i) S)).length ≤ 6 := by sorry


end Couret.STROBO2TORS
