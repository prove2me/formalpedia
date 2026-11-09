-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_squareFibre_union_at_most_two_orbits
-- name    : Couret.STROBO2TORS.recoh_squareFibre_union_at_most_two_orbits
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:56:57.030955+00:00
-- url     : https://prove2.me/theorems/38956248-9c33-4ee2-9f74-3a8a61288a39
-- title:
--   A triple square fibre is the union of at most two torsion orbits
-- statement:
--   Let $G$ be an abelian group, $P_\chi(A)=\sum_{x\in A}\chi(x)$, $R_A(z)=|\{(x,y)\in A^2:x+y=z\}|$, $F(A)=\{B:|B|=3,R_B=R_A\}$ and $O(A)=\{A+u:2u=0\}$. Assume $G$ finite and $|A|=3$. Then
--
--   $$\exists B,\quad F(A)=O(A)\cup O(B).$$
--
--   The two orbits may coincide; the statement does not assert that $B$ differs from $A$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/60f6d03fdb26a2498e9e856b49f93ad590b99409/research/strobo-2tors-2026-10-12/lean/RecohConditionalOrbitBridge.lean#L15-L41, lines 15–41; source file SHA-256 77fd85e465aec792a492c75e9897831873146f28bdd5d5b45cdb4fa78369f8b0; theorem Couret.STROBO2TORS.recoh_squareFibre_union_at_most_two_orbits

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_distinct_doubles_no_exception
import Theorems.Thm_Couret_STROBO2TORS_paired_squareFibre_eq
import Theorems.Thm_Couret_STROBO2TORS_same_doubles_no_exception
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_eq_orbit_of_no_exception
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58

set_option autoImplicit false

/-!
RECOH conditional bank: bridge to the STROBO orbit decomposition.
DRAFT: not compiled. This theorem reuses existing STROBO classification.
Clean branch based on main; independently compile with Lean 4.29.1.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem recoh_squareFibre_union_at_most_two_orbits
    (S : Finset G) (hS : S.card = 3) :
    ∃ T : Finset G,
      squareFibre S = torsionOrbit S ∪ torsionOrbit T := by sorry



end Couret.STROBO2TORS
