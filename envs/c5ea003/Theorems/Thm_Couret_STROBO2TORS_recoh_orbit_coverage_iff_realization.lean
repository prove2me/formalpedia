-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_orbit_coverage_iff_realization
-- name    : Couret.STROBO2TORS.recoh_orbit_coverage_iff_realization
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:55:45.194617+00:00
-- url     : https://prove2.me/theorems/eb4e57d8-477c-4a39-8239-bf6cad752b3d
-- title:
--   Sound and complete representatives characterize realizations
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Let $R:G\to\mathbb N$ and $\mathcal R$ a finite family of supports. Assume every $B\in\mathcal R$ has three elements and $Q_B=R$, and every three-element realization of $R$ is an $H$-translate of a member of $\mathcal R$. Then for every finite support $S$, $$\exists B\in\mathcal R,\exists u\in H,\ S=B+u\iff |S|=3\text{ and }Q_S=R.$$
--
--   This is the orbit-coverage contract in exact form.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCompactOrbitBridge.lean, lines 157–169; source file SHA-256 2210812918f698e754a80bfa765d762150858f96b474bf87485ecfd69522196f; theorem Couret.STROBO2TORS.recoh_orbit_coverage_iff_realization

import Aesop
import Definitions.Def_Couret_RecohCompactOrbitBridge_59017063a1ce
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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_realization_of_ordinary_partner
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a

set_option autoImplicit false

/-!
An anchored orbit test and a finite-list deduplication invariant.

The orbit test fixes one point of the left support and examines only the
points of the right support. It therefore examines three differences when
the right support has cardinal three. No ambient-group search is used.

The list routine retains the last representative of each orbit. This is a
deliberate model at the quotient level, not an assertion that its order or
chosen representatives equal the Python routine's first-retention order.
The results below concern represented orbits and pairwise inequivalence.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_orbit_coverage_iff_realization
    (R : G → ℕ) (reps : Finset (Finset G))
    (hsound : ∀ B ∈ reps, B.card = 3 ∧ orderedSquare B = R)
    (hcomplete : ∀ S : Finset G, S.card = 3 → orderedSquare S = R →
      ∃ B ∈ reps, OrdinaryPartner B S) (S : Finset G) :
    (∃ B ∈ reps, OrdinaryPartner B S) ↔ S.card = 3 ∧ orderedSquare S = R := by sorry


section Finite

variable [Fintype G]





end Finite

end Couret.STROBO2TORS
