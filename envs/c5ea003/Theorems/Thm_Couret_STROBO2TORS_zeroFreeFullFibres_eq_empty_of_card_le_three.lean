-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_empty_of_card_le_three
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_eq_empty_of_card_le_three
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:45.283687+00:00
-- url     : https://prove2.me/theorems/f97ad330-01cc-4c91-94fe-d47d1235930f
-- title:
--   Groups of size at most three have no zero-free triple fibres
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. If $N\le3$, then
--
--   $$\mathcal F^*=\varnothing,$$
--
--   where $\mathcal F^*$ is the collection of nonempty zero-free full triple square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsMaximumCases.lean, lines 217–236; source file SHA-256 1bfee4188b3c47a03a161a1e69038d93494311971f5cf01ae94bd27298727282; theorem Couret.STROBO2TORS.zeroFreeFullFibres_eq_empty_of_card_le_three

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_support_card_and_zero
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeFullFibres_eq_empty_of_card_le_three
    (hn : Fintype.card G ≤ 3) :
    (zeroFreeFullFibres : Finset (Finset (Finset G))) = ∅ := by sorry



end Finite
end Couret.STROBO2TORS
