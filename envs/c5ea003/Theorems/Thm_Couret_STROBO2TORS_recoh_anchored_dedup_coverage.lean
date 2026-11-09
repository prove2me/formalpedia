-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_anchored_dedup_coverage
-- name    : Couret.STROBO2TORS.recoh_anchored_dedup_coverage
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:18:51.96219+00:00
-- url     : https://prove2.me/theorems/073799cc-d7f2-496e-92e2-aa3242993798
-- title:
--   Anchored deduplication preserves ordinary-orbit coverage
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Assume $G$ finite. Let $x$ be a finite list of supports and $a$ an anchor function with $a(B)\in B$ for each list member. For every support $S$, $$\exists B\in\operatorname{dedup}_a(x),\ S=B+u\ (u\in H)\iff\exists B\in x,\ S=B+u\ (u\in H).$$
--
--   This retains exactly the same ordinary translation coverage.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCompactOrbitBridge.lean, lines 85–114; source file SHA-256 2210812918f698e754a80bfa765d762150858f96b474bf87485ecfd69522196f; theorem Couret.STROBO2TORS.recoh_anchored_dedup_coverage

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_anchored_dedup_mem_source
import Theorems.Thm_Couret_STROBO2TORS_recoh_anchored_orbit_check_iff
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

theorem recoh_anchored_dedup_coverage (anchor : Finset G → G)
    (xs : List (Finset G)) (hanchor : ∀ B ∈ xs, anchor B ∈ B)
    (S : Finset G) :
    (∃ B ∈ recohAnchoredOrbitDedup anchor xs, OrdinaryPartner B S) ↔
      ∃ B ∈ xs, OrdinaryPartner B S := by sorry










section Finite

variable [Fintype G]





end Finite

end Couret.STROBO2TORS
