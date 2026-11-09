-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_fibre_orbit_separator
-- name    : Couret.STROBO2TORS.recoh_cyclic_fibre_orbit_separator
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:00:42.038209+00:00
-- url     : https://prove2.me/theorems/3880fb59-8105-4a17-9359-50a61d96aa68
-- title:
--   One ternary coordinate separates the two possible torsion orbits
-- statement:
--   Let $d\in\mathbb N$, let $q_0,\ldots,q_{d-1}$ be positive integers, and put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. Let supplied three-primary factor data define the coordinate character bank, and let $S\subseteq G$ have three elements. Either every two members of $\mathcal F(S)$ are two-torsion translates, or there is a three-primary coordinate $i$ such that
--
--   $$B,C\in\mathcal F(S),\quad P_{\chi_i^{(3)}}(B)=P_{\chi_i^{(3)}}(C)\Longrightarrow C=B+u\text{ for some }2u=0.$$
--
--   This reduces orbit discrimination in a fixed square fibre to one chosen ternary measurement.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTernaryFibreSelector.lean, lines 92–121; source file SHA-256 a19004cdbc2c8dfeac9a2b85c2dced7eb2ccc647c2d5a1cbe660309ae6612e56; theorem Couret.STROBO2TORS.recoh_cyclic_fibre_orbit_separator

import Aesop
import Definitions.Def_Couret_RecohTernaryFibreSelector_4c0db0f29983
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_param_fibre_selected_separator
import Theorems.Thm_Couret_STROBO2TORS_recoh_exceptional_normal_form
import Theorems.Thm_Couret_STROBO2TORS_recoh_ordinary_partner_of_common_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_two_h_iff_exception
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
import Definitions.Def_Couret_RecohTernarySelector_13a2b1134dfc
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883

set_option autoImplicit false

/-!
A single concrete ternary coordinate separates the two translation orbits
of any exceptional triple fibre in a product of cyclic groups. The witness
comes from the executable direction selector. The conclusion quantifies over
the entire fibre, so the later square-only search may use any complete set
of orbit representatives rather than knowing the hidden support.
-/

namespace Couret.STROBO2TORS



variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_cyclic_fibre_orbit_separator
    (data3 : RecohPrimaryFactorData q 3)
    (S : Finset ((j : Fin d) → ZMod (q j))) (hS : S.card = 3) :
    (∀ B ∈ squareFibre S, ∀ C ∈ squareFibre S, OrdinaryPartner B C) ∨
      ∃ i : RecohPrimaryCoordinate q 3,
        ∀ B ∈ squareFibre S, ∀ C ∈ squareFibre S,
          recohSupportProbe (recohCyclicPrimaryBank q 3 data3 i) B =
            recohSupportProbe (recohCyclicPrimaryBank q 3 data3 i) C →
          OrdinaryPartner B C := by sorry


end Couret.STROBO2TORS
