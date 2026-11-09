-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_normalised_nonaffine
-- name    : Couret.InterIA.Catalogue.AffineTransport.normalised_nonaffine
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:49.189203+00:00
-- url     : https://prove2.me/theorems/9860d2be-e73e-4a47-9455-6606472b4b5f
-- title:
--   normalised nonaffine
-- statement:
--   For every natural number $n$, finite subsets $S,T,A,B$ of $ℤ/nℤ$, unit $u$, and residues $v,t$, suppose $A=uS+v$ and $B=u(T+t)+v$. If no unit $a$ and residue $b$ satisfy $aS+b=T$, then no unit $a$ and residue $b$ satisfy $aA+b=B$. This includes $n=0$ and empty sets.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineEquivalenceTransport.lean, lines 66–74; source file SHA-256 317b8b661cceb15b156cd289602ed84565c6a27bf8af9028f7e0389c60f5aab8; theorem Couret.InterIA.Catalogue.AffineTransport.normalised_nonaffine

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
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_common_affine_equivalent_iff
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_unilateral_translation_equivalent_iff
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.AffineTransport
open Finset Couret.InterIA.NormalForm

theorem normalised_nonaffine {n : ℕ} (S T A B : Finset (ZMod n))
    (u : (ZMod n)ˣ) (v t : ZMod n)
    (hS : S.image (fun z => (u : ZMod n)*z+v)=A)
    (hT : (T.image (fun z => z+t)).image (fun z => (u : ZMod n)*z+v)=B)
    (h : ¬ AffineEquivalent S T) : ¬ AffineEquivalent A B := by sorry


end Couret.InterIA.Catalogue.AffineTransport
