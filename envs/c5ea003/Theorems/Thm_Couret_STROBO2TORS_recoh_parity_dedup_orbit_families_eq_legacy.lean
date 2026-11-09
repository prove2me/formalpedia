-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_orbit_families_eq_legacy
-- name    : Couret.STROBO2TORS.recoh_parity_dedup_orbit_families_eq_legacy
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:17.080612+00:00
-- url     : https://prove2.me/theorems/d2e51f16-20f7-40d2-b0b5-219af5ee185e
-- title:
--   Parity deduplication preserves legacy orbit families
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S$ counts ordered sums and $B$ is a bank of complex additive characters. Assume $G$ finite. Let $U\subseteq G$ be finite, $R:G\to\mathbb N$ supported in $U$, and $h$ a sound and complete partial solver for doubling. Let a finite list $x$ have finite-set contents exactly the parity representatives for $(U,R,h)$. Let $a$ select a point in each member of $x$. Then $$\{\operatorname{Orb}_H(S):S\in\operatorname{dedup}_a(x)\}=\{\operatorname{Orb}_H(S):S\in\operatorname{LegacyReps}(U,R,h)\}.$$
--
--   This compares orbit families, with duplicate orbits removed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityOrbitRefinement.lean, lines 62–78; source file SHA-256 185cc0d31c6488113857d44700e65389fdc92fe2ab3f45b213f4e762f52ee979; theorem Couret.STROBO2TORS.recoh_parity_dedup_orbit_families_eq_legacy

import Aesop
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_cover
import Definitions.Def_Couret_RecohParityGenerator_deb90a4bb68d
import Definitions.Def_Couret_RecohCompactOrbitBridge_59017063a1ce

set_option autoImplicit false

/-!
Composition of the parity generator with the historical orbit construction.

The equality below is an equality of finite families of entire H-orbits,
not equality of representatives or their iteration order. Deduplication is
applied to an explicit list enumeration of the parity representatives. The
list and its anchors are inputs with stated representation contracts; no
classical `Finset.toList` is hidden in an executable definition.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem recoh_parity_dedup_orbit_families_eq_legacy
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (hhalf : RecohHalfSolverSpec half) (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (xs : List (Finset G))
    (hxs : xs.toFinset = recohParityRepresentatives U R half)
    (anchor : Finset G → G) (hanchor : ∀ B ∈ xs, anchor B ∈ B) :
    (recohAnchoredOrbitDedup anchor xs).toFinset.image torsionOrbit =
      (recohSquareRepresentatives U R half).image torsionOrbit := by sorry


section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]









end Cyclic

end Couret.STROBO2TORS
