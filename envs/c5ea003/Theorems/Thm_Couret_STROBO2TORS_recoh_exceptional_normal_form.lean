-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_exceptional_normal_form
-- name    : Couret.STROBO2TORS.recoh_exceptional_normal_form
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:35.297488+00:00
-- url     : https://prove2.me/theorems/f5041c65-febd-488b-a0d2-c3c2bfc5e367
-- title:
--   Every exceptional partner pair has normalized three-torsion parameters
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a support $S$, $P_\chi(S)=\sum_{s\in S}\chi(s)$, and $F(S)=\{T:|T|=3,R_T=R_S\}$. Put $H=G[2]$. If $S,T$ are exceptional partners, then there exist $a,d,v,u\in G$, with $d\ne0$, $2d=0$, $v\ne0$, $3v=0$ and $2u=0$, such that
--
--   $$S=\{a,a+v,a+v+d\},\qquad T=\{a,a-v,a-v+d\}+u.$$
--
--   No finiteness or zero-exclusion assumption is made.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohReconstruction.lean, lines 43–102; source file SHA-256 513a4060ff87ff1fa62542ec6ee81bb251e2eebfa05d359dd9f60f5fb115b612; theorem Couret.STROBO2TORS.recoh_exceptional_normal_form

import Aesop
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_triple_sum_translate
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
RECOH: reconstructing a cardinality-three support from its labelled ordered
square and a fixed bank of individual complex character coefficients.

The observation and the support cardinality are explicit. The classification
used below is the existing STROBO theorem, not an additional hypothesis.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_exceptional_normal_form (S T : Finset G)
    (he : ExceptionalPartner S T) :
    ∃ a d v u : G, d + d = 0 ∧ d ≠ 0 ∧
      (v + v) + v = 0 ∧ v ≠ 0 ∧ u + u = 0 ∧
      S = paramSupport ((a, d), v) ∧
      T = translateSupport (paramSupport ((a, d), -v)) u := by sorry












end Couret.STROBO2TORS
