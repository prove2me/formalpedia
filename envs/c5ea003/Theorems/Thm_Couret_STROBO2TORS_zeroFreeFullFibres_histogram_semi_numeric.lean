-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_histogram_semi_numeric
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_histogram_semi_numeric
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:44:02.976548+00:00
-- url     : https://prove2.me/theorems/96375e5a-5a55-417d-b568-f7a5a24de694
-- title:
--   Semi-numeric histogram of zero-free fibre sizes
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $\mathcal Z$ be the observed nonempty zero-free full fibres, let $\mathcal U$ be ordinary full fibres, and let $s=|\{\{v,-v\}:v\in K\setminus\{0\}\}|$. For $k>0$,
--
--   $$\#\{R\in\mathcal Z:|R|=k\}=\#\{F\in\mathcal U:|F^\circ|=k\}+[k=2h-2]3(h-1)s+[k=2h](q-3)(h-1)s.$$
--
--   Brackets denote indicators and $q-3$ uses natural subtraction.
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFreeAll.lean, lines 249–266; source file SHA-256 57e0e6b2919f605519cfad328e82e56477cae03c002010fa3c4fd6a8c218120b; theorem Couret.STROBO2TORS.zeroFreeFullFibres_histogram_semi_numeric

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_histogram_formula
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_histogram_partition
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_filter_card_pos
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeFullFibres_histogram_semi_numeric (k : ℕ) (hk : 0 < k) :
    ((zeroFreeFullFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = k)).card =
    ((ordinaryFibres : Finset (Finset (Finset G))).filter
      (fun F => (withoutZero F).card = k)).card +
    (if k = 2 * (twoTorsion : Finset G).card - 2 then
      3 * ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card else 0) +
    (if k = 2 * (twoTorsion : Finset G).card then
      ((doublingImages : Finset G).card - 3) *
        ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card else 0) := by sorry




/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS
