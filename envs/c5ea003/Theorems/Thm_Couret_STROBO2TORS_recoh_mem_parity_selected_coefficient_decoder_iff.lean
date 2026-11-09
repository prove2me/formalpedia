-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_mem_parity_selected_coefficient_decoder_iff
-- name    : Couret.STROBO2TORS.recoh_mem_parity_selected_coefficient_decoder_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:18:05.123043+00:00
-- url     : https://prove2.me/theorems/773d30e0-86e0-4d5b-bafd-362142d9bb5f
-- title:
--   Exact membership in the parity-selected coefficient decoder
-- statement:
--   Let $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$ for positive natural moduli $q_j$. The selected input format requires all $q_j\ge2$, $|G|\ge3$, a sparse square list of length three through six with distinct positions, multiplicities between one and three summing to nine, one or three odd multiplicities, and coefficient lists with distinct exponents below their assigned primary degree and nonzero coefficients. Let $E$ be the square-entry list, $L$ the coefficient lists indexed by the parity-selected bank, and $S$ any finite support. Interpret the input as $o=(R_E,v_L)$ and let $\chi$ be that selected bank. Then
--
--   $$S\in\operatorname{ParityDecoder}(q,E,L)\iff\operatorname{Format}(q,E,L)\land|S|=3\land(R_S,(P_{\chi_i}(S))_i)=o.$$
--
--   Malformed inputs accept no support.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDecoder.lean, lines 519–532; source file SHA-256 9726528ae3811835f453edf79765026c8ce160b6454c01ab77b6971e40840b98; theorem Couret.STROBO2TORS.recoh_mem_parity_selected_coefficient_decoder_iff

import Aesop
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_coefficient_core_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_input_check_iff
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c
import Definitions.Def_Couret_RecohParitySelector_0eb69704c517

set_option autoImplicit false

/-!
Coefficient decoding from the compact parity family.

The generic bridge uses a proved cover modulo two-torsion, the historical
sign-recovery specification and the exact integer observation checker.
The new candidate construction is an image of the parity family, not the
historical edge-triple enumeration. Definitions enumerate neither G nor
its two-torsion subgroup. Complex values occur only in the specification.
-/

namespace Couret.STROBO2TORS

variable {G I J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2













variable [Fintype I]







section CyclicSelected

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_mem_parity_selected_coefficient_decoder_iff
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (S : Finset ((i : Fin d) → ZMod (q i))) :
    S ∈ recohParitySelectedCoefficientDecoder q entries terms ↔
      RecohParitySelectedInputFormat q entries terms ∧ S.card = 3 ∧
        recohObservation (recohParitySelectedObservedBank q entries) S =
          recohParitySelectedTypedObservation q entries terms := by sorry








end CyclicSelected

end Couret.STROBO2TORS
