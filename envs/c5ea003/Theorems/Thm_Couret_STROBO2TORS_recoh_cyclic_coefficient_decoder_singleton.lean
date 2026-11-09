-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_coefficient_decoder_singleton
-- name    : Couret.STROBO2TORS.recoh_cyclic_coefficient_decoder_singleton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:30.792543+00:00
-- url     : https://prove2.me/theorems/b2a34d8c-f749-4a84-8168-b1f19c813199
-- title:
--   A valid realized cyclic input decodes to its unique triple
-- statement:
--   Let $d\in\mathbb N$ and let $q_0,\ldots,q_{d-1}$ be positive natural moduli. Put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. The primary-$p$ coordinate bank uses the standard character at the full $p$-power factor of each modulus divisible by $p$, with supplied factorization $q_j=p^{k_j+1}c_j$ and $\gcd(p,c_j)=1$. Let $E$ be sparse square entries and $L_i$ observed coefficient lists satisfying the cyclic input format: each $q_j\ge2$, the product of moduli is at least three, the sparse square list meets its prescribed format, and each coefficient list has reduced distinct exponents and nonzero coefficients. If a three-element support $S$ has exactly the interpreted square and canonical-bank readings, then
--
--   $$\operatorname{CoefficientDecoder}(q,E,L)=\{S\}.$$
--
--   The decoder therefore returns the unique realizing support.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicCoefficientDecoder.lean, lines 236–248; source file SHA-256 28a7b086d267426fb1e0879ed74d17a1d11a1d82cadf2b7320c0a89680767395; theorem Couret.STROBO2TORS.recoh_cyclic_coefficient_decoder_singleton

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_coefficient_decoder_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_observed_bank_injective
import Theorems.Thm_Couret_STROBO2TORS_recoh_exact_decoder_singleton
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8
import Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a

set_option autoImplicit false

/-!
An instantiated RECOH decoder on typed observations of cyclic products.

The user supplies only the moduli, labelled square entries, and the observed
coefficient lists.  The primary parameters, exponent encoders, binary
coordinates, doubling solver, square-value function and its covering set
are constructed here.  Their correctness contracts are all discharged.

There is one binary slot for every even factor. Ternary slots occur only
when some factor is even, exactly as for the fixed bank in the Python
decoder. The input guard also imposes moduli at least two, group order at
least three, and the typed numeric/uniqueness checks of its observation
readers. JSON syntax, machine execution and serialization remain separate.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_cyclic_coefficient_decoder_singleton
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms)
    (hformat : RecohCyclicInputFormat q entries terms)
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hobs : recohObservation (recohCyclicObservedBank q) S =
      recohCyclicTypedObservation q entries terms) :
    recohCyclicCoefficientDecoder q entries terms = {S} := by sorry






end Couret.STROBO2TORS
