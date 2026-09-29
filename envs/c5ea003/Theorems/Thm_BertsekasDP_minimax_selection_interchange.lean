-- Prove2me | Theorems.Thm_BertsekasDP_minimax_selection_interchange
-- name    : BertsekasDP.minimax_selection_interchange
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-04T16:51:41.349031+00:00
-- url     : https://prove2.me/theorems/4dc2a66b-6a10-49c2-a8a1-b0b1da80e657
-- title:
--   Min–max interchange over selection functions (Lemma 1.6.1)
-- statement:
--   **Lemma 1.6.1 (interchange of minimization and maximization).** Let $W$ and $U$ be arbitrary sets and let $G : W \times U \to \overline{\mathbb{R}}$ take values in the extended reals. Assume that for every $w \in W$ the pointwise infimum is not $-\infty$:
--
--   $$\inf_{u \in U} G(w,u) \;>\; -\infty \qquad \text{for all } w \in W.$$
--
--   Then minimization over *selection functions* may be interchanged with maximization over $w$:
--
--   $$\inf_{\mu : W \to U} \; \sup_{w \in W} \; G\bigl(w, \mu(w)\bigr) \;=\; \sup_{w \in W} \; \inf_{u \in U} G(w,u).$$
--
--   Here $\mu$ ranges over all functions assigning a $u$-value to each $w$, with no restriction whatsoever.
--
--   The inequality $\ge$ is the trivial direction and holds always; the content is the reverse one, and it is what allows the minimax dynamic programming algorithm to be derived stage by stage — at each stage the controller's choice may be resolved before the adversary's, provided no stage value is $-\infty$. The hypothesis is not decorative: without it the two sides can differ.
--
--   **Formalization Note** Both sides are lattice extrema in $\overline{\mathbb{R}} = \mathbb{R} \cup \{\pm\infty\}$, so they always exist but need not be attained; $G$ itself may take infinite values. The degenerate cases are included: with $U$ empty and $W$ nonempty both sides are $+\infty$, and with $W$ empty both sides are $-\infty$.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Lemma 1.6.1 (Section 1.6); statement reconstructed from its use in the derivation of the minimax DP algorithm

import Mathlib

namespace BertsekasDP

theorem minimax_selection_interchange {W U : Type} (G : W → U → EReal)
    (h : ∀ w, ⨅ u, G w u ≠ ⊥) :
    ⨅ μ : W → U, ⨆ w, G w (μ w) = ⨆ w, ⨅ u, G w u := by sorry

end BertsekasDP
