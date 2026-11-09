-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_prepared_candidates_le_twenty
-- name    : Couret.STROBO2TORS.recoh_cyclic_prepared_candidates_le_twenty
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:41.134597+00:00
-- url     : https://prove2.me/theorems/dba217a1-748d-46c9-92ed-bfa355dc4bc2
-- title:
--   The prepared cyclic candidate set has at most twenty members
-- statement:
--   Let $d\in\mathbb N$, let $q_0,\ldots,q_{d-1}$ be positive integers, and put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. The input has $q_j\ge2$ and $|G|\ge3$. Its square-entry list has between three and six distinct points, multiplicities in $\{1,2,3\}$ totaling nine, and either one or three odd multiplicities. Each coefficient list has distinct exponents, nonzero integer coefficients, and exponents below $(p-1)p^k$ for its primary root of order $p^{k+1}$. For a finite set $U\subseteq G$, a partial halving function $h:G\to G\cup\{\mathrm{none}\}$ and a recovery map $f$, fast candidates are $f(\{\sigma-e:e\in E\})$ for three-subsets $E\subseteq U$ on which $h(\sum E)=\sigma$ is defined. Apply the canonical product halving solver and indexed coefficient-sign recovery; in the prepared version also apply its early sparse-square and reading check. Then
--
--   $$|\mathcal C|\le20.$$
--
--   This bounds the generated candidates for every input satisfying the stated format.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicPreparedDecoder.lean, lines 121–135; source file SHA-256 ce438f7797a7d8114b2cc91e6f9398133f55bd0477b80c4f3fbaf12545a1e818; theorem Couret.STROBO2TORS.recoh_cyclic_prepared_candidates_le_twenty

import Aesop
import Definitions.Def_Couret_RecohCyclicPreparedDecoder_0ae8cdf0a932
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_fast_candidates_card_le_twenty
import Theorems.Thm_Couret_STROBO2TORS_recoh_typed_square_support_card_le_six
import Definitions.Def_Couret_RecohCyclicCoefficientDecoder_9d7602a6d6c9
import Definitions.Def_Couret_RecohEarlySignChecks_6186d05e32eb

set_option autoImplicit false

/-!
The concrete cyclic decoder with early square and reading checks.

All bank parameters, coefficient encodings, binary coordinates, and square
support data are constructed by the cyclic interface.  This module uses
those data in the early-rejection control flow: check the representative's
square and binary/ternary readings, recover its translation, then retain the
independent full final check.  The guarded decoder is equal to the complete
typed coefficient decoder for every input, including rejected input.

The equality relates executable Lean definitions on typed data.  It does
not identify the external Python parser, caches, or runtime with those
definitions, nor does the candidate bound assert bit complexity.
-/

namespace Couret.STROBO2TORS

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_cyclic_prepared_candidates_le_twenty
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms)
    (hformat : RecohCyclicInputFormat q entries terms) :
    (recohPreparedFastCandidates (recohTypedSquareSupport entries) (recohProductHalf q)
      (recohIndexedRecoverSupport (recohProductTwoCoordinates q)
        (recohCoefficientSignBools Sum.inl (recohCyclicBankPrime q)
          (recohCyclicBankDepth q) (recohCyclicBankEncoding q) terms))
      (recohEarlyCandidateCheck (recohTypedSquareSupport entries)
        (recohTypedSquareValue entries) (recohCyclicBankPrime q)
        (recohCyclicBankDepth q) (recohCyclicBankEncoding q) terms)).card ≤ 20 := by sorry


end Couret.STROBO2TORS
