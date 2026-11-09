-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslatedNeighbours_card_ordinary
-- name    : Couret.STROBO2TORS.nontranslatedNeighbours_card_ordinary
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:27.754171+00:00
-- url     : https://prove2.me/theorems/1021a672-b2fa-4f12-983d-7a752aff75ff
-- title:
--   Ordinary supports have no nontranslation neighbours
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. If $S$ has three elements and is not exceptional, then
--
--   $$|\mathcal F(S)\setminus\mathcal O(S)|=0.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationDegree.lean, lines 59–66; source file SHA-256 bb81c661856c1b823aeeb307e2603c5cb0aee20a082885d1c0ea1a2cc7b78ead; theorem Couret.STROBO2TORS.nontranslatedNeighbours_card_ordinary

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
import Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem nontranslatedNeighbours_card_ordinary (S : Finset G)
    (hS : S.card = 3)
    (hNotExc : S ∉ (exceptionalSupports : Finset (Finset G))) :
    (nontranslatedNeighbours S).card = 0 := by sorry








end Couret.STROBO2TORS
