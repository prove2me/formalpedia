-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_coefficient_decoder_singleton
-- name    : Couret.STROBO2TORS.recoh_parity_selected_coefficient_decoder_singleton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:09.972366+00:00
-- url     : https://prove2.me/theorems/10145628-fa89-4cb0-aa00-bb0eb37e09e0
-- title:
--   Parity-selected decoding recovers an actual triple uniquely
-- statement:
--   Let $d\ge0$, let $q_i$ be nonzero natural numbers for $i<d$, and set $A=\prod_{i<d}\mathbb Z/q_i$. A primary coordinate for a prime $p$ is an index with $p\mid q_i$. For supports in $A$, write $Q_S$ for ordered-sum counts, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a character bank $B$. Let $E$ be typed square entries on $A$ and $L_i$ sparse terms for the parity-selected bank, satisfying the defined parity-selected input format. If $S\subseteq A$ has three elements and its bank observation equals the typed observation, then $$D_{\mathrm{parity\ selected}}(E,L)=\{S\}.$$
--
--   This asserts existence and uniqueness for actual well-formed observations.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDecoder.lean, lines 547–559; source file SHA-256 9726528ae3811835f453edf79765026c8ce160b6454c01ab77b6971e40840b98; theorem Couret.STROBO2TORS.recoh_parity_selected_coefficient_decoder_singleton

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_coefficient_decoder_eq_legacy
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_input_format_iff_legacy
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_observation_iff_legacy
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_coefficient_decoder_singleton
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

theorem recoh_parity_selected_coefficient_decoder_singleton
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (hformat : RecohParitySelectedInputFormat q entries terms)
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hobs : recohObservation (recohParitySelectedObservedBank q entries) S =
      recohParitySelectedTypedObservation q entries terms) :
    recohParitySelectedCoefficientDecoder q entries terms = {S} := by sorry




end CyclicSelected

end Couret.STROBO2TORS
