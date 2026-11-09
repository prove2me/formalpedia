-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_mem_orderedNontranslationPairs
-- name    : Couret.STROBO2TORS.mem_orderedNontranslationPairs
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:31.596568+00:00
-- url     : https://prove2.me/theorems/e3ccc83d-ac4e-45f7-9667-95ebfa1f1df1
-- title:
--   Membership in the ordered nontranslation collision list
-- statement:
--   Let $G$ be a finite abelian group and $S,T\subseteq G$ finite. Write $Q_S(z)=|\{(x,y)\in S^2:x+y=z\}|$, retaining ordered pairs and diagonals. Let $\mathcal P$ be the finite enumeration obtained by filtering all ordered pairs of three-element supports by the nontranslation-collision predicate. Then $$(S,T)\in\mathcal P\iff |S|=|T|=3,\quad0\notin S,\quad0\notin T,\quad Q_S=Q_T,\quad\neg\exists u\in G,\ T=S+u.$$ Here $S+u=\{x+u:x\in S\}$. This connects the finite enumeration to its exact semantic predicate.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsPairCount.lean, lines 328–331; source file SHA-256 f6c997c461f640aab1856a21d5adfad3e6bfdbf876e67e5783b3ba87b26827cd; theorem Couret.STROBO2TORS.mem_orderedNontranslationPairs

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
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
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

theorem mem_orderedNontranslationPairs (S T : Finset G) :
    (S,T) ∈ orderedNontranslationPairs ↔ NontranslationCollision S T := by sorry


























end Finite
end Couret.STROBO2TORS
