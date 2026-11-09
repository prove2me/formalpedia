-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_selected_decoder_card_le_one
-- name    : Couret.STROBO2TORS.recoh_parity_dedup_selected_decoder_card_le_one
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:04.573307+00:00
-- url     : https://prove2.me/theorems/9e47d23d-0c8a-4f34-bba3-72abaae1439a
-- title:
--   The orbit-deduplicated selected decoder returns at most one support
-- statement:
--   Let $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$ for positive natural moduli $q_j$. Let $E$ be any sparse square entries, $L$ any coefficient lists of the parity-selected bank, and $X$ a list whose underlying set equals the cyclic parity representatives computed from $E$. Let an anchor map choose a member of each support in $X$. Then
--
--   $$|\operatorname{ParityDedupDecoder}(q,E,L,X,\operatorname{anchor})|\le1.$$
--
--   No input-format or reduced-coefficient hypothesis is required for this output-cardinality bound.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDedupTransport.lean, lines 264–273; source file SHA-256 dd13e6ade9a021706d0ec14fbcbb837eac41d9018980c650ddd694417386b379; theorem Couret.STROBO2TORS.recoh_parity_dedup_selected_decoder_card_le_one

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_selected_core_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_coefficient_core_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_coefficient_decoder_card_le_one
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_input_check_iff
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

theorem recoh_parity_dedup_selected_decoder_card_le_one
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (xs : List (Finset ((i : Fin d) → ZMod (q i))))
    (hxs : xs.toFinset = recohCyclicParityRepresentatives q entries)
    (anchor : Finset ((i : Fin d) → ZMod (q i)) → ((i : Fin d) → ZMod (q i)))
    (hanchor : ∀ B ∈ xs, anchor B ∈ B) :
    (recohParityDedupSelectedDecoder q entries terms xs anchor).card ≤ 1 := by sorry


end CyclicSelected

end Couret.STROBO2TORS
