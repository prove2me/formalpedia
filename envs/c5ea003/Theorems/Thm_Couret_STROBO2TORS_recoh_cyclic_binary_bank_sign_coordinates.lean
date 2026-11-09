-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_binary_bank_sign_coordinates
-- name    : Couret.STROBO2TORS.recoh_cyclic_binary_bank_sign_coordinates
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:06.927187+00:00
-- url     : https://prove2.me/theorems/fc9d2247-bce4-48bd-aabc-d3e18b2b90fa
-- title:
--   The cyclic binary bank reads two-torsion signs
-- statement:
--   Let $d\in\mathbb N$, let $q_0,\ldots,q_{d-1}$ be positive integers, and put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. Let the supplied two-primary factor data factor each even modulus into its exact power of two and odd coprime cofactor. Let $u\in G[2]$ and $i$ be an even coordinate. In the standard binary-coordinate equivalence $e:G[2]\cong\mathbb F_2^{\{i:2\mid q_i\}}$,
--
--   $$\chi_i^{(2)}(u)=\begin{cases}1,&e(u)_i=0,\\-1,&e(u)_i\ne0.\end{cases}$$
--
--   This connects the cyclic primary bank to translation recovery bits.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicPrimaryBank.lean, lines 230–250; source file SHA-256 430ca92ba25f4e25a54832978a347c9b3d98aef6735383f4f28b9a4fdaae66a1; theorem Couret.STROBO2TORS.recoh_cyclic_binary_bank_sign_coordinates

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_coordinate_kernel
import Theorems.Thm_Couret_STROBO2TORS_recoh_product_two_coordinates_eq_zero_iff
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

theorem recoh_cyclic_binary_bank_sign_coordinates
    (data : RecohPrimaryFactorData q 2)
    (u : recohTorsionSubgroup (G := (j : Fin d) → ZMod (q j)) 2)
    (i : RecohEvenCoordinate q) :
    recohCyclicPrimaryBank q 2 data i u.val =
      if recohProductTwoCoordinates q u i = 0 then 1 else -1 := by sorry
















end Couret.STROBO2TORS
