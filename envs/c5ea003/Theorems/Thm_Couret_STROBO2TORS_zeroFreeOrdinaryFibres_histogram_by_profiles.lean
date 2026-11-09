-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_histogram_by_profiles
-- name    : Couret.STROBO2TORS.zeroFreeOrdinaryFibres_histogram_by_profiles
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:50.588994+00:00
-- url     : https://prove2.me/theorems/9238ed34-9d02-4d13-88cd-db3590b209f8
-- title:
--   Ordinary zero-free histogram from four profiles
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For natural $k>0$, $$|\{F\in\mathcal O^\circ:|F|=k\}|=\sum_{j=0}^{3}1_{h-j=k}|\mathcal O_j|.$$ Every subtraction $h-j$ is truncated in the natural numbers. The positive-size hypothesis is explicit.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsClosedHistogram.lean, lines 116–173; source file SHA-256 584fb4d377d4eb190f2bc36949a4c3596cb755c509c4441a3e6c1c3c26d6477c; theorem Couret.STROBO2TORS.zeroFreeOrdinaryFibres_histogram_by_profiles

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
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_size_filter_card
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_eq_profile_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_filter_card_pos
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeOrdinaryFibres_histogram_by_profiles (k : ℕ) (hk : 0 < k) :
    ((zeroFreeOrdinaryFibres : Finset (Finset (Finset G))).filter
      (fun F => F.card = k)).card =
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
