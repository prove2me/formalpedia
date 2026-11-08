-- Prove2me | Theorems.Thm_ZeroExtensionGap_theorem_3_nash_williams
-- name    : ZeroExtensionGap.theorem_3_nash_williams
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:12.660978+00:00
-- url     : https://prove2.me/theorems/2f2a14a6-5783-4daa-b449-e13d4c0305b7
-- title:
--   Theorem 3 (Nash–Williams [NW64], cited) — partition into $a$ forests
-- statement:
--   Let $G=(V,E)$ be a multigraph without self-loops, and let $a\ge1$ be an integer. The edge set $E$ can be partitioned into $a$ forests if and only if
--
--   $$|E(G[S])|\le a(|S|-1)$$
--
--   for every $S\subseteq V$ with $|S|\ge2$. This classical result is cited, and is the source of the forest distributions of §5.1.
--
--   Differences from the source:
--   - encoding: a multigraph, finite by the title of [NW64], partitioned into $a$ forests → `ends : E → Sym2 V` on finite types and a colouring `c : E → Fin a` whose classes are forests; reason: the same partitions; a class may be empty
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Theorem 3, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ZeroExtensionGap_MGraph

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Theorem 3 (Nash–Williams [NW64]), p.22 (PDF p.24). A cited result, on a finite multigraph
without self-loops given by `ends : E → Sym2 V`; both directions.
**Formalization Note.** A partition into `a` forests is a colouring `c : E → Fin a`, and a class may be
empty. `|E(G[S])|` counts with multiplicity. -/
theorem theorem_3_nash_williams {V E : Type*} [Fintype V] [Fintype E] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (a : ℕ) (ha : 1 ≤ a) :
    (∃ c : E → Fin a, ∀ i, MIsForest ends {e | c e = i}) ↔
      ∀ S : Finset V, 2 ≤ S.card →
        (mEdgeCount ends S : ℝ) ≤ (a : ℝ) * ((S.card : ℝ) - 1) := by sorry

end ZeroExtensionGap
