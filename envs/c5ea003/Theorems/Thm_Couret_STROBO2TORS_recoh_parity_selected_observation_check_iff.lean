-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_observation_check_iff
-- name    : Couret.STROBO2TORS.recoh_parity_selected_observation_check_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:28:23.495433+00:00
-- url     : https://prove2.me/theorems/6c5f6d9b-9c2f-41a0-9127-368219bd1bf1
-- title:
--   The parity-selected coefficient check is semantically exact
-- statement:
--   Let $d\ge0$, let $q_i$ be nonzero natural numbers for $i<d$, and set $A=\prod_{i<d}\mathbb Z/q_i$. A primary coordinate for a prime $p$ is an index with $p\mid q_i$. For supports in $A$, write $Q_S$ for ordered-sum counts, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a character bank $B$. For typed square entries $E$ on $A$, terms $L_i$ indexed by the parity-selected bank, and any finite $S\subseteq A$, assume every term exponent is below the corresponding degree $(p_i-1)p_i^{k_i}$. Then $$\operatorname{check}_{\mathrm{coeff}}(E,L,S)=\mathrm{true}\iff\mathcal O_B(S)=\operatorname{TypedObs}(E,L).$$
--
--   The check uses the selected square support, typed square value, and parity-selected encodings.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDecoder.lean, lines 329–359; source file SHA-256 9726528ae3811835f453edf79765026c8ce160b6454c01ab77b6971e40840b98; theorem Couret.STROBO2TORS.recoh_parity_selected_observation_check_iff

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_observation_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_bank_encoding_interpret
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_bank_prime
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_bank_root_primitive
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

theorem recoh_parity_selected_observation_check_iff
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (hred : ∀ i, RecohCoefficientsReduced
      (recohParitySelectedBankPrime q entries i)
      (recohParitySelectedBankDepth q entries i) (terms i))
    (S : Finset ((i : Fin d) → ZMod (q i))) :
    recohCoefficientObservationCheck (recohSelectedSquareSupport q entries)
      (recohTypedSquareValue entries) (recohParitySelectedBankPrime q entries)
      (recohParitySelectedBankDepth q entries)
      (recohParitySelectedBankEncoding q entries) terms S = true ↔
        recohObservation (recohParitySelectedObservedBank q entries) S =
          recohParitySelectedTypedObservation q entries terms := by sorry






























end CyclicSelected

end Couret.STROBO2TORS
