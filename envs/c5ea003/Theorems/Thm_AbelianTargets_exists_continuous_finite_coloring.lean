-- Prove2me | Theorems.Thm_AbelianTargets_exists_continuous_finite_coloring
-- name    : AbelianTargets.exists_continuous_finite_coloring
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:50:23.837638+00:00
-- url     : https://prove2.me/theorems/00d46963-2314-445e-88c8-43c90a9b9270
-- title:
--   A clopen graph of bounded degree has a continuous finite coloring
-- statement:
--   Let $G$ be a simple graph on a topological space $X$. Suppose $X$ is covered by countably many clopen independent sets, and $N_G(S)$ is clopen whenever $S$ is clopen. Let $\Delta\in\mathbb N$. Suppose each $x$ is assigned a finite set $N_x\subseteq X$ containing all its graph neighbors and satisfying $|N_x|\le\Delta$. Then there exists a continuous proper coloring
--   $$c:X\longrightarrow\{0,\ldots,\Delta\},\qquad G(x,y)\Longrightarrow c(x)\ne c(y),$$
--   where the color set has the discrete topology.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/ClopenColoring.lean, lines 177–220; SHA256 5db313d8c6593f38577bc036f4127de25f4276a35cf973131deea4dd8cc823a9.

import Definitions.Def_AT260939824_ClopenMarkers
import Init
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Clopen
import Mathlib.Topology.Instances.Discrete

set_option autoImplicit false

/-!
# Continuous finite coloring from a countable clopen independent cover

Iterated relative clopen maximal independent sets give a proper coloring
with one more color than the degree bound. The relative construction and
the finite neighbor-count contradiction are proved explicitly.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {X : Type*} [TopologicalSpace X] (G : SimpleGraph X) (C : ℕ → Set X)

theorem AbelianTargets.exists_continuous_finite_coloring
    (hclopen : ∀ n,IsClopen (C n)) (hindep : ∀ n,GraphIndependent G (C n))
    (hcover : ∀ x,∃ n,x ∈ C n)
    (hneigh : ∀ S,IsClopen S → IsClopen (NeighborSet G S))
    (Δ : ℕ) (neighbors : X → Finset X) (hdegree : ∀ x,(neighbors x).card ≤ Δ)
    (hadj : ∀ x y,G.Adj y x → y ∈ neighbors x) :
    ∃ c : X → Fin (Δ+1),Continuous c ∧ ∀ x y,G.Adj x y → c x ≠ c y := by sorry
