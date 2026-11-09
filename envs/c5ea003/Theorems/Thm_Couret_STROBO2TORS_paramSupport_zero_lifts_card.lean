-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_paramSupport_zero_lifts_card
-- name    : Couret.STROBO2TORS.paramSupport_zero_lifts_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:24.981469+00:00
-- url     : https://prove2.me/theorems/cadaddf5-c4de-4edb-9def-f19c128e09a7
-- title:
--   Three anchors make a parameter support contain zero
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Put $P(a,d,v)=\{a,a+v,a+v+d\}$. Fix $d\in H\setminus\{0\}$ and $v\in K\setminus\{0\}$. Then
--
--   $$\#\{a\in G:0\in P(a,d,v)\}=3.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 151–156; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.paramSupport_zero_lifts_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_card
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_zero_lifts
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem paramSupport_zero_lifts_card (d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    ((Finset.univ : Finset G).filter (fun a => 0 ∈ paramSupport ((a, d), v))).card = 3 := by sorry
























































end Finite
end Couret.STROBO2TORS
