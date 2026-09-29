-- Prove2me | Theorems.Thm_mme_modern_complete_split_interval_acceptance
-- name    : mme_modern_complete_split_interval_acceptance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T17:22:53.228063+00:00
-- url     : https://prove2.me/theorems/ef0c33f4-4fdf-4a3d-9330-8be4016cdb29
-- title:
--   Complete-split interval acceptance preserves the source aggregate and slack
-- statement:
--   Let \(G\) be a finite set of groups, each with finitely many nodes, and let \(J\) be a finite set of leaves. For three coordinate directions \(d\in\{0,1,2\}\), define
--   $$E(a)=\sum_{g\in G}w_g\min_d\sum_{i\in I_g}a_{g,i,d},
--   \qquad M(b)=\min_d\sum_{j\in J}b_{j,d}.$$
--   Assume \(w_g\ge0\), pointwise lower bounds \(\underline a\le a\) and \(\underline b\le b\), nonnegative \(\Omega,s\), and a logarithm enclosure \(L\le U\). For every real margin \(\delta\),
--   $$sU+\delta\le E(\underline a)+M(\underline b)\Omega
--   \quad\Longrightarrow\quad
--   sL+\delta\le E(a)+M(b)\Omega.$$
--   Thus directed bounds certify the complete-split aggregate while preserving the full margin and the source's order of sums and minima. This is a finite algebraic checker implication; entropy enclosures, actual data feasibility, and tensor extraction must be established separately.
-- source:
--   Dupont et al., Improving the matrix multiplication exponent with modern optimization and AlphaEvolve, https://arxiv.org/abs/2608.16884v1, Sections 2.3-2.5: group minima after node sums, final Equation (11), and replacement by certified entropy upper bounds. The aggregation is shared with the More Asymmetry analysis.

import Mathlib.Tactic

set_option autoImplicit false

open BigOperators

universe u v w

theorem mme_modern_complete_split_interval_acceptance
    {G : Type u} {I : G → Type v} {J : Type w}
    [Fintype G] [∀ g, Fintype (I g)] [Fintype J]
    (weight : G → ℝ)
    (nodeLower nodeActual : (g : G) → I g → Fin 3 → ℝ)
    (leafLower leafActual : J → Fin 3 → ℝ)
    (Omega scale logActual logUpper margin : ℝ)
    (hweight : ∀ g, 0 ≤ weight g)
    (hnode : ∀ g i d, nodeLower g i d ≤ nodeActual g i d)
    (hleaf : ∀ j d, leafLower j d ≤ leafActual j d)
    (hOmega : 0 ≤ Omega) (hscale : 0 ≤ scale)
    (hlog : logActual ≤ logUpper)
    (hcertificate :
      scale * logUpper + margin ≤
        (∑ g, weight g *
          min (∑ i, nodeLower g i 0)
            (min (∑ i, nodeLower g i 1) (∑ i, nodeLower g i 2))) +
        min (∑ j, leafLower j 0)
          (min (∑ j, leafLower j 1) (∑ j, leafLower j 2)) * Omega) :
    scale * logActual + margin ≤
      (∑ g, weight g *
        min (∑ i, nodeActual g i 0)
          (min (∑ i, nodeActual g i 1) (∑ i, nodeActual g i 2))) +
      min (∑ j, leafActual j 0)
        (min (∑ j, leafActual j 1) (∑ j, leafActual j 2)) * Omega := by sorry
