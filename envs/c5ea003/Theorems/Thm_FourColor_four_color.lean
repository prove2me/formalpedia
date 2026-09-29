-- Prove2me | Theorems.Thm_FourColor_four_color
-- name    : FourColor.four_color
-- status  : Open
-- author  : @Minghui
-- created : 2026-09-26T19:26:04.455233+00:00
-- url     : https://prove2.me/theorems/8247cfb9-1636-4cf1-a05f-220bae0de50a
-- title:
--   Four Color Theorem for finite planar graphs
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
--   For every finite vertex type $V$ and every simple graph $G$ on $V$,
--   $$\operatorname{IsPlanar}(G)\Longrightarrow
--   \exists c:V\to\{0,1,2,3\},\quad
--   \forall v,w,\ G(v,w)\Longrightarrow c(v)\ne c(w).$$
--   All four colors need not be used. Empty graphs, isolated vertices and disconnected
--   graphs are included; no connectedness, degree bound, chosen vertex enumeration,
--   or decidability hypothesis is imposed. This is an existence theorem for proper
--   vertex colorings. The adjacency representation does not distinguish parallel
--   edges. A development using explicit multigraphs must justify the transfer.
--
--   Formalization note: the standard graph formulation of the source theorem.
--   Mathlib supplies `SimpleGraph` and `Colorable`; planarity is independently
--   defined by topological drawings. If proved through hypermaps, all graph
--   realization and color-transport steps must be formalized. The draft is an open
--   target; checking its statement does not prove it. Source: Robertson, Sanders, Seymour, Thomas, The Four-Colour Theorem, JCTB 70(1), 2–44 (1997), https://doi.org/10.1006/jctb.1997.1750; author manuscript https://people.math.gatech.edu/~thomas/PAP/fc.pdf, PDF p. 2, Section 1, paragraph 1 (unnumbered Four-Colour Theorem), and PDF p. 3, Section 2, drawing conventions. Gonthier, A Computer-Checked Proof of the Four Colour Theorem (2005), https://www.microsoft.com/en-us/research/wp-content/uploads/2012/10/4colproof.pdf, PDF p. 4, Section 2, paragraph beginning 'Although the statement' (graph embedding discussion; no numbered equation).
-- source:
--   Robertson, Sanders, Seymour, Thomas, The Four-Colour Theorem, JCTB 70(1), 2–44 (1997), https://doi.org/10.1006/jctb.1997.1750; author manuscript https://people.math.gatech.edu/~thomas/PAP/fc.pdf, PDF p. 2, Section 1, paragraph 1 (unnumbered Four-Colour Theorem), and PDF p. 3, Section 2, drawing conventions. Gonthier, A Computer-Checked Proof of the Four Colour Theorem (2005), https://www.microsoft.com/en-us/research/wp-content/uploads/2012/10/4colproof.pdf, PDF p. 4, Section 2, paragraph beginning 'Although the statement' (graph embedding discussion; no numbered equation).

import Definitions.Def_FourColor_PlaneDrawing

namespace FourColor
universe u
theorem four_color :
  ∀ (V : Type u) [Finite V] (G : SimpleGraph V), IsPlanar G → G.Colorable 4 := by sorry
end FourColor
