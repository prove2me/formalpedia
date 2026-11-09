-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion
-- name    : Couret.STROBO2TORS.zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:44.286343+00:00
-- url     : https://prove2.me/theorems/913f22e5-22f5-44bc-ae41-4abb675c1be6
-- title:
--   No nontrivial three-torsion means no zero-free exceptional fibres
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. If $t=1$, then the collection $\mathcal E^*=\{F^*:F\text{ exceptional}\}$ satisfies
--
--   $$\mathcal E^*=\varnothing.$$
--
--   This excludes the entire exceptional branch.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsMaximumCases.lean, lines 12–22; source file SHA-256 1bfee4188b3c47a03a161a1e69038d93494311971f5cf01ae94bd27298727282; theorem Couret.STROBO2TORS.zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_numeric
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion
    (ht : (threeTorsion : Finset G).card = 1) :
    (zeroFreeExceptionalFibres : Finset (Finset (Finset G))) = ∅ := by sorry



























end Finite
end Couret.STROBO2TORS
