-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
-- name    : Couret.STROBO2TORS.recoh_support_probe_three
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:45.117+00:00
-- url     : https://prove2.me/theorems/e8ba117e-5ff0-48ed-b302-065f624cd357
-- title:
--   The character reading of three distinct points
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $R_S$ the ordered pair-sum count of a finite support, and $P_\chi(S)=\sum_{s\in S}\chi(s)$. For pairwise distinct $a,b,c\in G$ and any complex additive character $\chi$,
--
--   $$P_\chi(\{a,b,c\})=\chi(a)+\chi(b)+\chi(c).$$
--
--   Distinctness prevents finite-set duplicate removal from changing the three-term sum.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohReconstruction.lean, lines 27–30; source file SHA-256 513a4060ff87ff1fa62542ec6ee81bb251e2eebfa05d359dd9f60f5fb115b612; theorem Couret.STROBO2TORS.recoh_support_probe_three

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

theorem recoh_support_probe_three (chi : AddChar G ℂ) (a b c : G)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    recohSupportProbe chi {a, b, c} = chi a + chi b + chi c := by sorry
















end Couret.STROBO2TORS
