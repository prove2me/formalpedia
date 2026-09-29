-- Prove2me | Definitions.Def_YogeshwaranDM_CompleteMatching
-- name    : YogeshwaranDM_CompleteMatching
-- status  : Definition
-- author  : @wamlart
-- created : 2026-09-06T01:42:52.5119+00:00
-- url     : https://prove2.me/theorems/6f7da5bd-644e-4162-ab19-845a8916f89e
-- title:
--   Definition 6.1 — Complete matching
-- statement:
--   **Definition 6.1 — Complete matching.** Let $G$ be a simple graph, $M$ a subgraph of $G$, and $S\subseteq V(G)$. The subgraph $M$ is a **complete matching on $S$** when every vertex of $M$ has exactly one neighbor in $M$, and $S\subseteq V(M)$.
--
--   **Formalization note.** The matching condition is Mathlib's native $M.\mathrm{IsMatching}$; a matching has no isolated vertices in its own vertex set. Isolated ambient vertices need not belong to $M$. The definition does not assert that $S$ is nonempty. Perfect matching retains Mathlib's existing native meaning: a spanning matching.
-- source:
--   D. Yogeshwaran, Discrete Mathematics—Lecture Notes, Indian Statistical Institute Bangalore, HTML edition generated May 9, 2025, Definition 6.1, https://www.isibang.ac.in/~d.yogesh/Course_Notes/DM1/Ch6.S1.html

import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false

namespace YogeshwaranDM

def CompleteMatching {V : Type*} {G : SimpleGraph V}
    (M : G.Subgraph) (S : Set V) : Prop :=
  M.IsMatching ∧ S ⊆ M.verts

end YogeshwaranDM


