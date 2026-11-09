-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationPairs_preimage
-- name    : Couret.STROBO2TORS.nontranslationPairs_preimage
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:46.685084+00:00
-- url     : https://prove2.me/theorems/ad450aa8-3374-414c-883a-472ad994d3fb
-- title:
--   Two orientations of each nontranslation pair
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For every member $P$ of the defined unordered nontranslation pair family, exactly two ordered nontranslation pairs $p$ have endpoint set $P$: $$|\{p:\{p_1,p_2\}=P\}|=2.$$
--
--   This is a fibre-cardinality statement for forgetting orientation.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsPairCount.lean, lines 374–396; source file SHA-256 f6c997c461f640aab1856a21d5adfad3e6bfdbf876e67e5783b3ba87b26827cd; theorem Couret.STROBO2TORS.nontranslationPairs_preimage

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
import Theorems.Thm_Couret_STROBO2TORS_NontranslationCollision_ne
import Theorems.Thm_Couret_STROBO2TORS_mem_orderedNontranslationPairs
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

theorem nontranslationPairs_preimage (P : Finset (Finset G)) (hP : P ∈ nontranslationPairs) :
    ((orderedNontranslationPairs : Finset (Finset G × Finset G)).filter
      (fun p => ({p.1,p.2} : Finset (Finset G))=P)).card = 2 := by sorry














end Finite
end Couret.STROBO2TORS
