-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_selected_core_eq_exact
-- name    : Couret.STROBO2TORS.recoh_parity_dedup_selected_core_eq_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:15.192377+00:00
-- url     : https://prove2.me/theorems/e820e3d7-fceb-45ab-8e4c-be459ae2148a
-- title:
--   Anchored deduplication preserves exact selected parity decoding
-- statement:
--   Let $d\in\mathbb N$, let $q_0,\ldots,q_{d-1}$ be positive integers, and put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. Let $L$ be a list whose underlying set is exactly the cyclic parity representatives of typed square entries. Let an anchor function choose a member of every support occurring in $L$. Let the sparse terms for the parity-selected bank have all exponents below their primary basis bound $(p_i-1)p_i^{k_i}$. Then
--
--   $$\operatorname{ParityDedupSelectedCore}(\mathrm{entries},T,L,\mathrm{anchor})=\operatorname{ExactDecoder}_{\rm parity\ selected}(\operatorname{TypedObs}(\mathrm{entries},T)).$$
--
--   No full input-format hypothesis is needed for this core equality.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDedupTransport.lean, lines 170–200; source file SHA-256 dd13e6ade9a021706d0ec14fbcbb837eac41d9018980c650ddd694417386b379; theorem Couret.STROBO2TORS.recoh_parity_dedup_selected_core_eq_exact

import Aesop
import Definitions.Def_Couret_RecohParityDedupTransport_fd9d6ec554ae
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_cover
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_observation_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_recovery_spec
import Theorems.Thm_Couret_STROBO2TORS_recoh_representative_checked_decoder_eq_exact
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06

set_option autoImplicit false

/-!
Transport through the explicit anchored deduplication model.

An enumeration and an anchor remain explicit inputs with representation
contracts. The decoder really recovers from the retained representatives.
The fibre classification bounds their number by two, without assuming that
the supplied square data are realizable. No Python list-order or JSON
equivalence is claimed by this module.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G I : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]











section CyclicSelected

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_parity_dedup_selected_core_eq_exact
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (xs : List (Finset ((i : Fin d) → ZMod (q i))))
    (hxs : xs.toFinset = recohCyclicParityRepresentatives q entries)
    (anchor : Finset ((i : Fin d) → ZMod (q i)) → ((i : Fin d) → ZMod (q i)))
    (hanchor : ∀ B ∈ xs, anchor B ∈ B)
    (hred : ∀ i, RecohCoefficientsReduced
      (recohParitySelectedBankPrime q entries i)
      (recohParitySelectedBankDepth q entries i) (terms i)) :
    recohParityDedupSelectedCore q entries terms xs anchor =
      recohExactDecoder (recohParitySelectedObservedBank q entries)
        (recohParitySelectedTypedObservation q entries terms) := by sorry












end CyclicSelected

end Couret.STROBO2TORS
