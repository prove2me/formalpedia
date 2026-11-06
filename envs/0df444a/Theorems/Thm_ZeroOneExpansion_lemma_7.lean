-- Prove2me | Theorems.Thm_ZeroOneExpansion_lemma_7
-- name    : ZeroOneExpansion.lemma_7
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:22:24.373658+00:00
-- url     : https://prove2.me/theorems/c7a2bf36-4039-40aa-90b0-57da7baaa590
-- title:
--   Lemma 7 — $P_n$ is full-dimensional: $\dim(P_n)=4n+1$
-- statement:
--   For every $n\ge1$, the polytope $P_n\subseteq\mathbb R^{4n+1}$ is full-dimensional:
--   $$\dim(P_n)=4n+1.$$
--
--   This converts a bound on $h(G_n)$ in terms of $n$ into one in terms of $\dim(P_n)$.
--
--   Differences from the source:
--   - encoding: dim(P) = dim(aff(P)) → Module.finrank ℝ (affineSpan ℝ P).direction; reason: the dimension of the affine hull
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Lemma 7, p.5

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn
import Definitions.Def_ZeroOneExpansion_polyDim

set_option autoImplicit false

namespace ZeroOneExpansion

/-- **Lemma 7** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.5). The polytope `Pn` is full-dimensional, i.e. `dim(Pn) = 4n + 1`.

**Formalization Note** §3 fixes `n ≥ 1`. `dim` is the dimension of the affine hull (`polyDim`). -/
theorem lemma_7 (n : ℕ) (hn : 1 ≤ n) : polyDim (Pn n) = 4 * n + 1 := by sorry

end ZeroOneExpansion
