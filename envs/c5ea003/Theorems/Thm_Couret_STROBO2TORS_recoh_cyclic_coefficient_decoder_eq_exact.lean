-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_coefficient_decoder_eq_exact
-- name    : Couret.STROBO2TORS.recoh_cyclic_coefficient_decoder_eq_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:27:33.087296+00:00
-- url     : https://prove2.me/theorems/1499a87b-53f5-472e-9a32-9ef5ba8f98b1
-- title:
--   The cyclic coefficient decoder equals exact decoding
-- statement:
--   Let $d\in\mathbb N$, let $q_0,\ldots,q_{d-1}$ be positive integers, and put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. The input has $q_j\ge2$ and $|G|\ge3$. Its square-entry list has between three and six distinct points, multiplicities in $\{1,2,3\}$ totaling nine, and either one or three odd multiplicities. Each coefficient list has distinct exponents, nonzero integer coefficients, and exponents below $(p-1)p^k$ for its primary root of order $p^{k+1}$. Use the canonical cyclic observed bank: one two-primary character per even coordinate, and three-primary characters at coordinates divisible by three when some modulus is even. Let $(R,o)$ be the typed observation read from the square entries and sparse coefficients. Then
--
--   $$\operatorname{CyclicCoefficientDecoder}(\mathrm{entries},T)=\operatorname{ExactDecoder}_{\rm cyclic}(R,o).$$
--
--   The decoder therefore returns exactly the compatible three-element supports.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicCoefficientDecoder.lean, lines 201–209; source file SHA-256 28a7b086d267426fb1e0879ed74d17a1d11a1d82cadf2b7320c0a89680767395; theorem Couret.STROBO2TORS.recoh_cyclic_coefficient_decoder_eq_exact

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_coefficient_core_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_input_check_iff
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

theorem recoh_cyclic_coefficient_decoder_eq_exact
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms)
    (hformat : RecohCyclicInputFormat q entries terms) :
    recohCyclicCoefficientDecoder q entries terms =
      recohExactDecoder (recohCyclicObservedBank q) (recohCyclicTypedObservation q entries terms) := by sorry












end Couret.STROBO2TORS
