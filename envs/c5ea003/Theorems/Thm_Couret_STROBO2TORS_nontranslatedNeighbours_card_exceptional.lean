-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslatedNeighbours_card_exceptional
-- name    : Couret.STROBO2TORS.nontranslatedNeighbours_card_exceptional
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:23.862439+00:00
-- url     : https://prove2.me/theorems/963ed1f4-8588-46cb-a6fb-9182efefcff0
-- title:
--   Nontranslation degree of an exceptional support
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. If $S\in\mathcal S_{\mathrm{exc}}$, then $$|N(S)|=h,$$ where $N(S)$ consists of square-collision neighbours that are not translates of $S$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsNontranslationDegree.lean, lines 50–57; source file SHA-256 bb81c661856c1b823aeeb307e2603c5cb0aee20a082885d1c0ea1a2cc7b78ead; theorem Couret.STROBO2TORS.nontranslatedNeighbours_card_exceptional

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem nontranslatedNeighbours_card_exceptional (S : Finset G)
    (hExc : S ∈ (exceptionalSupports : Finset (Finset G))) :
    (nontranslatedNeighbours S).card = (twoTorsion : Finset G).card := by sorry










end Couret.STROBO2TORS
