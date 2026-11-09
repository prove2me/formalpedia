-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
-- name    : Couret.STROBO2TORS.mem_tripleSupportsProfile
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:54:44.295604+00:00
-- url     : https://prove2.me/theorems/8642eb52-ec10-4af2-b9a6-553bc7961819
-- title:
--   Triple torsion-profile membership
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $\mathcal T_j$ denote triple supports with torsion profile $j$. For any finite support $S$ and $j\in\mathbb N$,
--
--   $$S\in\mathcal T_j\Longleftrightarrow |S|=3\text{ and }|S\cap H|=j.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFreeAll.lean, lines 345–348; source file SHA-256 57e0e6b2919f605519cfad328e82e56477cae03c002010fa3c4fd6a8c218120b; theorem Couret.STROBO2TORS.mem_tripleSupportsProfile

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]





































/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/

theorem mem_tripleSupportsProfile (S : Finset G) (j : ℕ) :
    S ∈ tripleSupportsProfile j ↔
      S.card = 3 ∧ (S ∩ (twoTorsion : Finset G)).card = j := by sorry




/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS
