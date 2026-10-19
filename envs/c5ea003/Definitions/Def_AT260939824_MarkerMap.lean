-- Prove2me | Definitions.Def_AT260939824_MarkerMap
-- name    : AT260939824_MarkerMap
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:42:49.621988+00:00
-- url     : https://prove2.me/theorems/ad945560-5281-4d87-9c41-3531f295735e
-- title:
--   Clopen orbit markers at one isotropic scale
-- statement:
--   Let $d,L\in\mathbb N$ and let $\mathbb Z^d$ act on a topological space $X$. Clopen marker data consist of a clopen set $A\subseteq X$ with the following two orbit properties. Writing $A_x=\{g\in\mathbb Z^d:g\cdot x\in A\}$, require
--   $$u,v\in A_x,\ u\ne v\ \Longrightarrow\ \exists i,\ L<|u_i-v_i|,$$
--   $$\forall u\in\mathbb Z^d\ \exists a\in A_x\ \forall i,\ |u_i-a_i|\le L.$$
--   Thus markers are separated at the common coordinate scale $L$ and cover every orbit within that scale. The structure itself assumes neither freeness nor continuity of the action and permits $d=0$ or $L=0$. It is the orbit-marker input for the finite-window map of Lemma 7.3.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Section 7, especially Lemma 7.3; https://arxiv.org/html/2609.39824v1#S7. Formalization-specific marker-data structure in the import closure of Theorem 1.4 and Proposition 7.1. Original Lean module AbelianTargets/MarkerMap.lean, selected declaration lines 16-25; SHA-256 34e5642cac497a2063c46289790c2cb913741940d8f334b821408dfd97aad98d. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# The continuous map into a finite marker graph

This file proves the positive window-map construction of Lemma 7.3 from
an actual clopen, separated, covering marker set. It does not assert
the existence of that marker set for an arbitrary free action.
-/

namespace AbelianTargets

noncomputable section

/-- The exact orbit marker data needed by the window-map construction. -/
structure ClopenMarkers (d L : ℕ) (X : Type*)
    [TopologicalSpace X] [AddAction (Lattice d) X] where
  carrier : Set X
  isClopen : IsClopen carrier
  separated : ∀ (x : X) (u v : Lattice d),
    u +ᵥ x ∈ carrier → v +ᵥ x ∈ carrier → u ≠ v →
      ∃ i, (L : ℤ) < |u i - v i|
  covering : ∀ (x : X) (u : Lattice d),
    ∃ a : Lattice d, a +ᵥ x ∈ carrier ∧ ∀ i, |u i - a i| ≤ (L : ℤ)

namespace ClopenMarkers

variable {d L : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]















end ClopenMarkers

end

end AbelianTargets


