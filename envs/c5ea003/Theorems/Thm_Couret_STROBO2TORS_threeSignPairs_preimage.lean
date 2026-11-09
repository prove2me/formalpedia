-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_threeSignPairs_preimage
-- name    : Couret.STROBO2TORS.threeSignPairs_preimage
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:13.239569+00:00
-- url     : https://prove2.me/theorems/fc910e30-5ae6-4a39-aff4-76ee09a67e9b
-- title:
--   A nonzero three-torsion sign pair is its own preimage
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For any member $P$ of the nonzero three-torsion sign-pair family, $$\{w\in K\setminus\{0\}:\{w,-w\}=P\}=P.$$
--
--   The two signs are exactly the elements realizing that pair.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 377–400; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.threeSignPairs_preimage

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem threeSignPairs_preimage (P : Finset G)
    (hP : P ∈ (threeSignPairs : Finset (Finset G))) :
    ((threeTorsion : Finset G).erase 0).filter (fun w => ({w, -w} : Finset G) = P) = P := by sorry




































end Finite
end Couret.STROBO2TORS
