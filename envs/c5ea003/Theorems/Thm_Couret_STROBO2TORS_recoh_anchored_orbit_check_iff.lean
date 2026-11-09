-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_anchored_orbit_check_iff
-- name    : Couret.STROBO2TORS.recoh_anchored_orbit_check_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:02:05.498913+00:00
-- url     : https://prove2.me/theorems/8787cff2-542d-4712-90e6-7ff30afee0da
-- title:
--   The anchored orbit check detects two-torsion translation
-- statement:
--   Let $G$ be an abelian group. Let $b_0\in B$, with $B,C$ finite supports. The anchored check searches $c\in C$ for a shift $c-b_0$ of order dividing two taking $B$ to $C$. Then
--
--   $$\operatorname{check}_{b_0}(B,C)=\mathrm{true}\Longleftrightarrow\exists u:\ 2u=0,\quad C=B+u.$$
--
--   Only the source anchor must be a member of its support.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCompactOrbitBridge.lean, lines 27–40; source file SHA-256 2210812918f698e754a80bfa765d762150858f96b474bf87485ecfd69522196f; theorem Couret.STROBO2TORS.recoh_anchored_orbit_check_iff

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

theorem recoh_anchored_orbit_check_iff (b₀ : G) (B C : Finset G)
    (hb₀ : b₀ ∈ B) :
    recohAnchoredOrbitCheck b₀ B C = true ↔ OrdinaryPartner B C := by sorry
























section Finite

variable [Fintype G]





end Finite

end Couret.STROBO2TORS
