-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_ternary_selected_detects
-- name    : Couret.STROBO2TORS.recoh_ternary_selected_detects
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:46:25.112978+00:00
-- url     : https://prove2.me/theorems/8789d18a-e8fa-4d8b-aec3-628a64dd5f5c
-- title:
--   The chosen ternary coordinate detects its parameter
-- statement:
--   Let $d\ge0$, let $q_i$ be nonzero natural numbers for $i<d$, and set $A=\prod_{i<d}\mathbb Z/q_i$. A primary coordinate for a prime $p$ is an index with $p\mid q_i$. For supports in $A$, write $Q_S$ for ordered-sum counts, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a character bank $B$. Given three-primary factor data and a nonzero $v\in A$ with $3v=0$, the deterministic selected coordinate $i(v)$ satisfies $$\chi_{i(v)}(v)\ne1.$$
--
--   This certifies the selected rather than merely an existential detecting coordinate.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTernarySelector.lean, lines 223–228; source file SHA-256 80e6d82f0d714a0a990e4cb06a522f263602edb4a6af0908e1b5acc52eaa9c1f; theorem Couret.STROBO2TORS.recoh_ternary_selected_detects

import Aesop
import Definitions.Def_Couret_RecohTernarySelector_13a2b1134dfc
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
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_coordinate_kernel
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a

set_option autoImplicit false

/-!
An executable coordinate selector for a supplied direction killed by three.
The search visits the labelled cyclic coordinates in increasing order and
returns the first nonzero coordinate whose modulus is divisible by three.
Only natural divisibility and equality in a cyclic group are tested.

The optional selector is defined on every input vector. The total selector
requires the direction to be nonzero and killed by three; its proof arguments
are erased during execution. Complex characters are used only to state the
semantic detection guarantee for the selected coordinate.
-/

namespace Couret.STROBO2TORS

variable {d : ℕ} (q : Fin d → ℕ)





























variable [∀ i, NeZero (q i)]

theorem recoh_ternary_selected_detects
    (data3 : RecohPrimaryFactorData q 3)
    (v : (i : Fin d) → ZMod (q i)) (hv : 3 • v = 0) (hv0 : v ≠ 0) :
    recohCyclicPrimaryBank q 3 data3 (recohTernaryCoordinate q v hv hv0) v ≠ 1 := by sorry






end Couret.STROBO2TORS
