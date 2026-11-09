-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_coordinate_kernel
-- name    : Couret.STROBO2TORS.recoh_cyclic_primary_coordinate_kernel
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:51.311195+00:00
-- url     : https://prove2.me/theorems/6b55ea28-68c9-41cc-b549-4d90baf32112
-- title:
--   Primary coordinate characters detect primary torsion
-- statement:
--   Let $d\in\mathbb N$, let $q_0,\ldots,q_{d-1}$ be positive integers, and put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. Let $p$ be prime, let supplied primary factor data factor $q_i$ into its exact $p$-power part and coprime cofactor, and let $i$ satisfy $p\mid q_i$. For any $x\in G$ with $p x_i=0$,
--
--   $$\chi_i^{(p)}(x)=1\Longleftrightarrow x_i=0.$$
--
--   This is faithfulness on the coordinate primary-torsion subgroup.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicPrimaryBank.lean, lines 179–205; source file SHA-256 430ca92ba25f4e25a54832978a347c9b3d98aef6735383f4f28b9a4fdaae66a1; theorem Couret.STROBO2TORS.recoh_cyclic_primary_coordinate_kernel

import Aesop
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a
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
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a
import Definitions.Def_Couret_RecohCyclicCoordinates_d669b2caaf1a
import Mathlib.Data.Multiset.Sort
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false

/-!
Coordinate primary characters and executable exponent encodings for finite
products of cyclic groups. The encoding sorts the multiset of coordinate
values, so multiplicities are retained and no enumeration of the ambient
group is used. Complex roots and characters are semantic objects; exponent
lists and primary-factor data are the inputs used by the exact backend.
-/

namespace Couret.STROBO2TORS





variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_cyclic_primary_coordinate_kernel (p : ℕ) [Fact p.Prime]
    (data : RecohPrimaryFactorData q p) (i : RecohPrimaryCoordinate q p)
    (x : (j : Fin d) → ZMod (q j)) (hx : p • x i.val = 0) :
    recohCyclicPrimaryBank q p data i x = 1 ↔ x i.val = 0 := by sorry






















end Couret.STROBO2TORS
