-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_ternary_coordinate_scan_first
-- name    : Couret.STROBO2TORS.recoh_ternary_coordinate_scan_first
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:20.662866+00:00
-- url     : https://prove2.me/theorems/2671079f-d611-420b-950b-e40607319a20
-- title:
--   The ternary scan returns the first eligible nonzero coordinate
-- statement:
--   Let $q_j$ be arbitrary natural moduli and $v\in\prod_{j<d}\mathbb Z/q_j\mathbb Z$. Let $L$ be any list of coordinate labels. If the specified ternary scan returns an eligible coordinate $i$ with $3\mid q_i$, then
--
--   $$\exists B,A,\quad L=B\mathbin{+\!+}[i]\mathbin{+\!+}A,\qquad\forall j\in B,\quad3\mid q_j\Longrightarrow v_j=0.$$
--
--   The list may repeat coordinates, and the moduli need not be positive for this scan-order property.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTernarySelector.lean, lines 77–101; source file SHA-256 80e6d82f0d714a0a990e4cb06a522f263602edb4a6af0908e1b5acc52eaa9c1f; theorem Couret.STROBO2TORS.recoh_ternary_coordinate_scan_first

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

theorem recoh_ternary_coordinate_scan_first
    (v : (i : Fin d) → ZMod (q i)) (labels : List (Fin d))
    (i : RecohPrimaryCoordinate q 3)
    (hs : recohTernaryCoordinateScan q v labels = some i) :
    ∃ before after : List (Fin d),
      labels = before ++ i.val :: after ∧
        ∀ j ∈ before, 3 ∣ q j → v j = 0 := by sorry
















variable [∀ i, NeZero (q i)]





















end Couret.STROBO2TORS
