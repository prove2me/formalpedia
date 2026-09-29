-- Prove2me | Definitions.Def_FourColor_PlaneDrawing
-- name    : FourColor_PlaneDrawing
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-26T19:25:50.013479+00:00
-- url     : https://prove2.me/theorems/e7e035ad-264f-4baf-9cbf-7b80bd9c828c
-- title:
--   Planar drawings of simple graphs in the real plane
-- statement:
--   Notation: $V$ is the vertex type, $G$ is a symmetric, irreflexive
--   adjacency relation, and $n = |V|$ is the vertex count when $V$ is finite. If
--   $\iota:V\to\mathbb R^2$ places the vertices, $p = \iota(v)$ denotes the point
--   representing a vertex $v$. Edges are continuous injective arcs on $[0,1]$ with
--   the prescribed endpoints, reversed consistently on reverse adjacency, avoiding
--   all other vertices; distinct undirected edges intersect only at shared endpoints.
--   The plane has its usual topology. There is no probability model.
--
--
--   A plane drawing is the data described above, and
--   $\operatorname{IsPlanar}(G)$ means such a drawing exists. The definition itself
--   does not assume finiteness; the mission theorem does. It neither mentions a
--   coloring nor assumes the result of any configuration checker.
--
--   Formalization note: a source-derived Lean encoding of the graph-embedding
--   formulation, using Mathlib paths and simple graphs. It is not a literal port of
--   Gonthier's topological-map or hypermap definitions. Source: Robertson, Sanders, Seymour, Thomas, The Four-Colour Theorem, JCTB 70(1), 2–44 (1997), https://doi.org/10.1006/jctb.1997.1750; author manuscript https://people.math.gatech.edu/~thomas/PAP/fc.pdf, PDF p. 2, Section 1, paragraph 1 (unnumbered Four-Colour Theorem), and PDF p. 3, Section 2, drawing conventions. Gonthier, A Computer-Checked Proof of the Four Colour Theorem (2005), https://www.microsoft.com/en-us/research/wp-content/uploads/2012/10/4colproof.pdf, PDF p. 4, Section 2, paragraph beginning 'Although the statement' (graph embedding discussion; no numbered equation).
-- source:
--   Robertson, Sanders, Seymour, Thomas, The Four-Colour Theorem, JCTB 70(1), 2–44 (1997), https://doi.org/10.1006/jctb.1997.1750; author manuscript https://people.math.gatech.edu/~thomas/PAP/fc.pdf, PDF p. 2, Section 1, paragraph 1 (unnumbered Four-Colour Theorem), and PDF p. 3, Section 2, drawing conventions. Gonthier, A Computer-Checked Proof of the Four Colour Theorem (2005), https://www.microsoft.com/en-us/research/wp-content/uploads/2012/10/4colproof.pdf, PDF p. 4, Section 2, paragraph beginning 'Although the statement' (graph embedding discussion; no numbered equation).

import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Topology.Path

/-!
A topological drawing of a simple graph in the real plane.
The definition is independent of coloring and of any reducibility certificate.
-/

namespace FourColor

universe u

/-- Vertices are distinct points, and edges are simple arcs that meet only at shared endpoints. -/
structure PlaneDrawing {V : Type u} (G : SimpleGraph V) where
  vertex : V → ℝ × ℝ
  vertex_injective : Function.Injective vertex
  arc : ∀ {v w : V}, G.Adj v w → Path (vertex v) (vertex w)
  arc_injective : ∀ {v w : V} (h : G.Adj v w), Function.Injective (arc h)
  arc_reverse : ∀ {v w : V} (h : G.Adj v w), arc (G.symm h) = (arc h).symm
  arc_avoids_vertices : ∀ {v w : V} (h : G.Adj v w) (t : unitInterval) (x : V),
    arc h t = vertex x → x = v ∨ x = w
  arcs_meet_only_at_endpoints :
    ∀ {v w x y : V} (h : G.Adj v w) (k : G.Adj x y) (s t : unitInterval),
      arc h s = arc k t →
        (v = x ∧ w = y) ∨ (v = y ∧ w = x) ∨
          ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1))

/-- Existence of a crossing-free drawing by simple continuous arcs in the real plane. -/
def IsPlanar {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (PlaneDrawing G)

end FourColor


