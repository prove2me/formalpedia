-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_cyclic_four_fibre_affine
-- name    : Couret.InterIA.Fibres.cyclic_four_fibre_affine
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:15.815455+00:00
-- url     : https://prove2.me/theorems/c1598cce-7369-45ec-b4c7-ba4095cbcd73
-- title:
--   The binary four-point fibre is affine
-- statement:
--   Let $n>0$ and $S\subseteq\mathbb Z/n$ have four elements. The binary indicator vectors of its cyclic four-point square fibre form an affine subspace $A$ over $\mathbb F_2$ with direction dimension $d\le2$, and $$|\mathcal F(S)|=2^d.$$
--
--   The equality identifies the underlying set of $A$ exactly with those indicators.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/BinaryAffineFibre.lean, lines 104–112; source file SHA-256 b920a719a42974e083f8586678ffbb9bb518599a9505a50ad0279045bdd7b28a; theorem Couret.InterIA.Fibres.cyclic_four_fibre_affine

import Definitions.Def_Couret_BinaryAffineFibre_5ba9c7ff8364
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Fibres_cyclic_four_fibre_card_pow_finrank
import Theorems.Thm_Couret_InterIA_Fibres_cyclic_four_fibre_ncard
import Definitions.Def_Couret_XorFibreClosure_3be6ba745ef2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

theorem cyclic_four_fibre_affine (n : ℕ) (hn : 0 < n)
    (S : Finset (ZMod n)) (hS : S.card=4) :
    ∃ A : AffineSubspace (ZMod 2) (ZMod n → ZMod 2),
      (A : Set (ZMod n → ZMod 2))=binaryIndicator '' cyclicFourFibre n S ∧
      Module.finrank (ZMod 2) A.direction ≤ 2 ∧
      (cyclicFourFibre n S).ncard=2^Module.finrank (ZMod 2) A.direction := by sorry


end Couret.InterIA.Fibres
