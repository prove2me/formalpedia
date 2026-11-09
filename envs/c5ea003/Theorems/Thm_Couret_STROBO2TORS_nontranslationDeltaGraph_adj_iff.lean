-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_adj_iff
-- name    : Couret.STROBO2TORS.nontranslationDeltaGraph_adj_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:36.312276+00:00
-- url     : https://prove2.me/theorems/60242162-4292-4601-931b-cc4c454b4a7b
-- title:
--   Adjacency in a nontranslation distance graph
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For finite supports $S,T$ and natural $k$, adjacency in $\Gamma^{\mathrm{nt}}_k$ holds exactly when $$|S|=|T|=3,\quad Q_S=Q_T,\quad T\ne S+u\ (u\in G),\quad |S\triangle T|=k.$$
--
--   The nontranslation condition itself excludes equality.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaExceptionalCount.lean, lines 53–63; source file SHA-256 f29a05e63c72c6391cb5af4eda72214b169f1bd248608234ab836d615b0d4ef0; theorem Couret.STROBO2TORS.nontranslationDeltaGraph_adj_iff

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaExceptionalCount_9f9783d90924
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374

set_option autoImplicit false

/-!
Unordered nontranslation collisions, split by symmetric-difference size.
The ambient group is finite abelian, supports have cardinality three, and
zero is permitted. An exceptional source has one delta-four neighbour and
`|G[2]| - 1` delta-six neighbours. Graph degree sums count unordered pairs
twice, so the final statements require no division in natural numbers.
-/

open scoped BigOperators symmDiff

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem nontranslationDeltaGraph_adj_iff (S T : Finset G) (k : ℕ) :
    (nontranslationDeltaGraph (G := G) k).Adj S T ↔
      S.card = 3 ∧ T.card = 3 ∧
        (∀ z : G, orderedSquare S z = orderedSquare T z) ∧
        (¬ ∃ v : G, T = translateSupport S v) ∧ (S ∆ T).card = k := by sorry

































end Couret.STROBO2TORS
