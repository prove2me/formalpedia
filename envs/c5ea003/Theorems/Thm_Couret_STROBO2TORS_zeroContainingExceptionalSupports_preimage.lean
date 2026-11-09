-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroContainingExceptionalSupports_preimage
-- name    : Couret.STROBO2TORS.zeroContainingExceptionalSupports_preimage
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:30.227205+00:00
-- url     : https://prove2.me/theorems/e5205e19-925a-48c0-a78f-81791375233c
-- title:
--   Zero-containing supports in an exceptional fibre
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For any exceptional fibre $F$, $$\{S\in\mathcal S_{\mathrm{exc},0\in S}:F(S)=F\}=\{S\in F:0\in S\}.$$
--
--   Here the subscript means exceptional supports containing zero, not profile zero.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 232–250; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.zeroContainingExceptionalSupports_preimage

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_preimage
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem zeroContainingExceptionalSupports_preimage (F : Finset (Finset G))
    (hF : F ∈ (exceptionalFibres : Finset (Finset (Finset G)))) :
    zeroContainingExceptionalSupports.filter (fun S : Finset G => squareFibre S = F) =
      F.filter (fun S => 0 ∈ S) := by sorry










































end Finite
end Couret.STROBO2TORS
