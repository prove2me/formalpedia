-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_eq_three_profile_union
-- name    : Couret.STROBO2TORS.exceptionalSupports_eq_three_profile_union
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:36.710425+00:00
-- url     : https://prove2.me/theorems/9a0df68c-72c9-483d-b00b-5e3d9408ea0d
-- title:
--   Exceptional supports have three possible profiles
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. Writing $\mathcal S_{\mathrm{exc},j}$ for exceptional supports meeting $H$ in $j$ points, $$\mathcal S_{\mathrm{exc}}=\mathcal S_{\mathrm{exc},0}\cup\mathcal S_{\mathrm{exc},1}\cup\mathcal S_{\mathrm{exc},2}.$$
--
--   This exhausts all exceptional supports.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsExceptionalZero.lean, lines 37–73; source file SHA-256 65617a4490b73497cb28359bad8f2b27cd3159569e95b4ec095e4f4604f5eca0; theorem Couret.STROBO2TORS.exceptionalSupports_eq_three_profile_union

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_three_eq_empty
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem exceptionalSupports_eq_three_profile_union :
    (exceptionalSupports : Finset (Finset G)) =
      exceptionalSupportsProfile 0 ∪
        (exceptionalSupportsProfile 1 ∪ exceptionalSupportsProfile 2) := by sorry










end Finite
end Couret.STROBO2TORS
