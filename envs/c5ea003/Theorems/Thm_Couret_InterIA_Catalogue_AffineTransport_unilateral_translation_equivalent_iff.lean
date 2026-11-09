-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_unilateral_translation_equivalent_iff
-- name    : Couret.InterIA.Catalogue.AffineTransport.unilateral_translation_equivalent_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:16.237797+00:00
-- url     : https://prove2.me/theorems/2b6be1c6-6ced-4e64-ac36-f9374fb3501a
-- title:
--   Translating one support
-- statement:
--   For every natural $n$, finite subsets $S,T$ of $R=\operatorname{ZMod}(n)$, and $t\in R$, there exist a unit $u$ and $v\in R$ with $uS+v=T+t$ if and only if there exist a unit $a$ and $b\in R$ with $aS+b=T$. Empty sets and $n=0$ (where $R=\mathbb Z$) are included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineEquivalenceTransport.lean, lines 56–64; source file SHA-256 317b8b661cceb15b156cd289602ed84565c6a27bf8af9028f7e0389c60f5aab8; theorem Couret.InterIA.Catalogue.AffineTransport.unilateral_translation_equivalent_iff

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_affine_equivalent_symm
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_affine_equivalent_trans
import Theorems.Thm_Couret_InterIA_NormalForm_translation_is_affine
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.AffineTransport
open Finset Couret.InterIA.NormalForm

theorem unilateral_translation_equivalent_iff {n : ℕ} (S T : Finset (ZMod n)) (t : ZMod n) :
    AffineEquivalent S (T.image (fun z => z+t)) ↔ AffineEquivalent S T := by sorry




end Couret.InterIA.Catalogue.AffineTransport
