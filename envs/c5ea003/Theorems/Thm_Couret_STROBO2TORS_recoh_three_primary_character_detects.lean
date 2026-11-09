-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_three_primary_character_detects
-- name    : Couret.STROBO2TORS.recoh_three_primary_character_detects
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:03:34.590366+00:00
-- url     : https://prove2.me/theorems/3182611d-5655-4569-a442-3cfc5af49312
-- title:
--   A primary-three character detects every nonzero three-torsion element
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $R_S$ the ordered pair-sum count of a finite support, and $P_\chi(S)=\sum_{s\in S}\chi(s)$. Assume $G$ finite, $v\ne0$ and $3v=0$. There is a complex additive character $\chi$ such that
--
--   $$\chi(v)\ne1,\qquad\forall u\in H,\ \chi(u)=1,\qquad\forall x\in G,\exists n\in\mathbb N,\ \chi(x)^{3^n}=1.$$
--
--   Thus detection can be chosen without seeing any two-torsion translation.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreUpper.lean, lines 79–102; source file SHA-256 682ad74687cb91c6b5c8d4f92be42d438a63b3a643e0e0c7a5093423d4d3efdc; theorem Couret.STROBO2TORS.recoh_three_primary_character_detects

import Aesop
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_three_primary_characters_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_torsion_subgroup_nsmul
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Data.Finite.Card

set_option autoImplicit false

/-!
Character banks chosen after the labelled ordered square has been observed.
The bank may depend on the complete square fibre, but is fixed on that fibre.
The ordinary fibre needs the two-torsion rank many character slots.  An
exceptional fibre needs at most one additional character slot, independently
of the three-torsion rank of the ambient finite abelian group.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem recoh_three_primary_character_detects (v : G)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    ∃ chi : AddChar G ℂ,
      (∀ x : G, ∃ n : ℕ, (chi x) ^ (3 ^ n) = 1) ∧
      (∀ u : G, u + u = 0 → chi u = 1) ∧ chi v ≠ 1 := by sorry










end Couret.STROBO2TORS
