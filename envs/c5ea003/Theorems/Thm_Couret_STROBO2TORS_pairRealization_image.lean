-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_pairRealization_image
-- name    : Couret.STROBO2TORS.pairRealization_image
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:09.728012+00:00
-- url     : https://prove2.me/theorems/b8ee8a48-c8ac-4cf9-ae0b-ffd24cac8940
-- title:
--   Pair parameters realize all ordered nontranslation pairs
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. The defined pair-parameter realization map has image $$\rho(\mathcal P)=P_{\mathrm{nt}}^{\mathrm{ordered}}.$$
--
--   This asserts surjectivity onto the specified finite family, without injectivity.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsPairCount.lean, lines 333–346; source file SHA-256 f6c997c461f640aab1856a21d5adfad3e6bfdbf876e67e5783b3ba87b26827cd; theorem Couret.STROBO2TORS.pairRealization_image

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_orderedNontranslationPairs
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_nontranslationCollision_param_iff
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]
































attribute [local instance] Classical.propDecidable

theorem pairRealization_image :
    (pairParameters : Finset (PairParameter G)).image pairRealization = orderedNontranslationPairs := by sorry
























end Finite
end Couret.STROBO2TORS
