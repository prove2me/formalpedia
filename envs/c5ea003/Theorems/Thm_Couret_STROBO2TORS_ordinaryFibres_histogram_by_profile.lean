-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_histogram_by_profile
-- name    : Couret.STROBO2TORS.ordinaryFibres_histogram_by_profile
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:40:31.990344+00:00
-- url     : https://prove2.me/theorems/d4e33ad3-a2b3-4527-9308-b5e554776afa
-- title:
--   The ordinary zero-free histogram splits into four profiles
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $O_j$ be the number of ordinary full fibres whose members meet $H$ in $j$ points. For every $k\in\mathbb N$,
--
--   $$|\{F\text{ ordinary}:|F^*|=k\}|=\sum_{j=0}^3\mathbf1_{h-j=k}O_j.$$
--
--   All four summands are retained even when truncated sizes coincide.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsHistogram.lean, lines 118–180; source file SHA-256 c12ab039c6b1ab4ff961876e1b2df183771e0e7ecfaff3c058cae2eec9da35b0; theorem Couret.STROBO2TORS.ordinaryFibres_histogram_by_profile

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibre_inter_twoTorsion_card_constant
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_filter_size_card
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_eq_profile_union_alternative
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem ordinaryFibres_histogram_by_profile (k : ℕ) :
    ((ordinaryFibres : Finset (Finset (Finset G))).filter
      (fun F => (withoutZero F).card = k)).card =
      (if (twoTorsion : Finset G).card = k then
        (ordinaryFibresProfile (G := G) 0).card else 0) +
      (if (twoTorsion : Finset G).card - 1 = k then
        (ordinaryFibresProfile (G := G) 1).card else 0) +
      (if (twoTorsion : Finset G).card - 2 = k then
        (ordinaryFibresProfile (G := G) 2).card else 0) +
      (if (twoTorsion : Finset G).card - 3 = k then
        (ordinaryFibresProfile (G := G) 3).card else 0) := by sorry




end Finite
end Couret.STROBO2TORS
