-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_anchored_dedup_mem_source
-- name    : Couret.STROBO2TORS.recoh_anchored_dedup_mem_source
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:55.492481+00:00
-- url     : https://prove2.me/theorems/e8c035fd-8f41-4f3e-847f-9471dc713c7e
-- title:
--   Orbit deduplication introduces no new supports
-- statement:
--   Let $G$ be an abelian group. Let an arbitrary anchor function assign a group element to each finite support, and let $L$ be any list of supports. If $B$ belongs to the anchored orbit-deduplicated list, then
--
--   $$B\in L.$$
--
--   This preserves the source-list membership of every retained representative.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCompactOrbitBridge.lean, lines 72–83; source file SHA-256 2210812918f698e754a80bfa765d762150858f96b474bf87485ecfd69522196f; theorem Couret.STROBO2TORS.recoh_anchored_dedup_mem_source

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

theorem recoh_anchored_dedup_mem_source (anchor : Finset G → G)
    (xs : List (Finset G)) (B : Finset G)
    (hB : B ∈ recohAnchoredOrbitDedup anchor xs) : B ∈ xs := by sorry












section Finite

variable [Fintype G]





end Finite

end Couret.STROBO2TORS
