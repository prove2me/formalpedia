-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_ordinary_partner_of_common_torsion_orbit
-- name    : Couret.STROBO2TORS.recoh_ordinary_partner_of_common_torsion_orbit
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:46.662014+00:00
-- url     : https://prove2.me/theorems/1bc4bb97-b8bb-4076-b8d1-ec352d138b73
-- title:
--   Members of a common torsion orbit are ordinary partners
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. For any finite support $P$ and $B,C\in\mathcal O(P)$,
--
--   $$\exists u\in H:\quad C=B+u.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTernaryFibreSelector.lean, lines 16–29; source file SHA-256 a19004cdbc2c8dfeac9a2b85c2dced7eb2ccc647c2d5a1cbe660309ae6612e56; theorem Couret.STROBO2TORS.recoh_ordinary_partner_of_common_torsion_orbit

import Aesop
import Definitions.Def_Couret_RecohTernaryFibreSelector_4c0db0f29983
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
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohTernarySelector_13a2b1134dfc
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883

set_option autoImplicit false

/-!
A single concrete ternary coordinate separates the two translation orbits
of any exceptional triple fibre in a product of cyclic groups. The witness
comes from the executable direction selector. The conclusion quantifies over
the entire fibre, so the later square-only search may use any complete set
of orbit representatives rather than knowing the hidden support.
-/

namespace Couret.STROBO2TORS

theorem recoh_ordinary_partner_of_common_torsion_orbit
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (P B C : Finset G)
    (hB : B ∈ torsionOrbit P) (hC : C ∈ torsionOrbit P) :
    OrdinaryPartner B C := by sorry


variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]







end Couret.STROBO2TORS
