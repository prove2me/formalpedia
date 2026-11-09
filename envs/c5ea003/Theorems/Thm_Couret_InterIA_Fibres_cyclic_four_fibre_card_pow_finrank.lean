-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_cyclic_four_fibre_card_pow_finrank
-- name    : Couret.InterIA.Fibres.cyclic_four_fibre_card_pow_finrank
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:41:17.378205+00:00
-- url     : https://prove2.me/theorems/56a0b05c-20a1-4fb9-b218-afc2f62f7516
-- title:
--   Cyclic four-support fibres have binary affine cardinality
-- statement:
--   Let $n>0$ and $S\subseteq\mathbb Z/n\mathbb Z$ have four elements. Let $\mathcal F(S)$ be the four-element supports with the same ordered-square counts as $S$. Their binary indicators form an affine subspace over $\mathbb F_2$; write $V$ for its direction space. Then
--
--   $$|\mathcal F(S)|=2^{\dim_{\mathbb F_2}V}.$$
--
--   This expresses ambiguity as binary affine dimension.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/BinaryAffineFibre.lean, lines 77–89; source file SHA-256 b920a719a42974e083f8586678ffbb9bb518599a9505a50ad0279045bdd7b28a; theorem Couret.InterIA.Fibres.cyclic_four_fibre_card_pow_finrank

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
import Definitions.Def_Couret_XorFibreClosure_3be6ba745ef2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

theorem cyclic_four_fibre_card_pow_finrank (n : ℕ) (hn : 0 < n)
    (S : Finset (ZMod n)) (hS : S.card=4) :
    (cyclicFourFibre n S).ncard=2^Module.finrank (ZMod 2) (cyclicFibreAffine n hn S hS).direction := by sorry






end Couret.InterIA.Fibres
