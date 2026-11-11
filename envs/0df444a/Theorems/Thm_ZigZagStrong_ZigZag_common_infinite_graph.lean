-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_common_infinite_graph
-- name    : ZigZagStrong.ZigZag.common_infinite_graph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:04:26.348314+00:00
-- url     : https://prove2.me/theorems/466f6b52-43d6-4db6-82a1-890640ac0de5
-- title:
--   Claim A.1 — label independence, covering, bipartiteness and symmetry
-- statement:
--   Suppose $H$ is vertex-transitive. Any two port labelings of the infinite $d$-regular tree give isomorphic zig-zag products. Denote this common graph by $X_H$. For every connected port-labeled $d$-regular graph $G$,
--   $$X_H\longrightarrow G\mathbin{z}H\quad\text{is a graph cover}.$$
--   Moreover $X_H$ is bipartite and
--   $$\operatorname{spec}(A_{X_H})=-\operatorname{spec}(A_{X_H}).$$
--   Graph isomorphisms preserve adjacency multiplicities. Covering is expressed by a surjective vertex map and local bijections on actual three-step zig-zag paths, commuting with path reversal. The canonical matching-tree realization supplies the bipartition and operator spectrum, without assuming that $X_H$ is connected.
--
--   Differences from the source:
--   - encoding: Graph isomorphism and graph covering of zig-zag multigraphs → Adjacency-count isomorphism and local bijections on three-step zig-zag paths commuting with actual path reversal; canonical free-product realization; reason: The tree products have no loops, so adjacency counts determine their multigraph isomorphism type. For covering targets, retaining the middle port and both gadget incidences preserves reversal even when it exchanges distinct orientations of a loop. Disconnected products remain allowed.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Claim A.1, p. 27.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem common_infinite_graph {d c : ℕ} (H : Gadget d c) (hv : VertexTransitive H) :
  (∀ (V W : Type*) [Infinite V] [Infinite W], ∀ P : PortGraph d V, ∀ Q : PortGraph d W,
    P.IsTree → Q.IsTree → ∃ e : (Fin d × V) ≃ (Fin d × W),
      ∀ x y, zigzagKernel H P x y = zigzagKernel H Q (e x) (e y)) ∧
  (∀ (V W : Type*) [Infinite V], ∀ P : PortGraph d V, ∀ G : PortGraph d W,
    P.IsTree → G.base.Connected →
    ∃ f : (Fin d × V) → (Fin d × W), Function.Surjective f ∧
      ∃ e : ∀ x y, ZigzagPath H P x y → ZigzagPath H G (f x) (f y),
        (∀ x y p, e y x (reverseZigzagPath p) = reverseZigzagPath (e x y p)) ∧
        (∀ x, Function.Bijective (fun z : (Σ y, ZigzagPath H P x y) =>
          (⟨f z.1, e x z.1 z.2⟩ : Σ y, ZigzagPath H G (f x) y)))) ∧
  (∃ color : (Fin d × FreeInvolutions d) → Bool,
    ∀ x y, 0 < matchingKernel H x y → color x ≠ color y) ∧
  spectrum ℂ (matchingLimit H) = (fun z : ℂ => -z) '' spectrum ℂ (matchingLimit H) := by sorry

end ZigZagStrong.ZigZag
