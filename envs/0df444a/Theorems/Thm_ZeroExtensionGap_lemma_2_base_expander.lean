-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_2_base_expander
-- name    : ZeroExtensionGap.lemma_2_base_expander
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:49.731035+00:00
-- url     : https://prove2.me/theorems/c502d548-4400-4bc7-b096-ce70fea48df0
-- title:
--   Lemma 2 — the base expander
-- statement:
--   Fix an integer $t\ge1$. There are constants $0<h_0\le1$, $\kappa>0$ and $0<\gamma\le\frac{1}{40000t\log(40t)}$ such that, for every sufficiently large even integer $n$, there is a simple graph $H$ on $n$ vertices with:
--
--   1. maximum degree at most $3$;
--   2. edge expansion at least $h_0$;
--   3. girth at least $\lfloor\gamma\log n\rfloor$;
--   4. unweighted diameter at most $\eta\log n$, where $\eta:=50/h_0$;
--   5. $\Gamma(H[S])\le1+\kappa/\log n$ for every $S\subseteq V(H)$ with $|S|\le n^{0.9}$.
--
--   $H$ is the core used at every level of the tower.
--
--   Differences from the source:
--   - encoding: a graph $H$ on $n$ vertices → `SimpleGraph (Fin n)`; reason: every $n$-element vertex set is a copy of `Fin n`
--   - encoding: $t$ fixed at the head of §3 → binder `t` with `1 ≤ t`; reason: standing assumption of the section, written out
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 2, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_ZeroExtensionGap_towerGraph

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 2, p.6 (PDF p.8). `t ≥ 1` is the standing integer of §3, p.5 (PDF p.7).
`BaseConstants` is the constants line of the lemma and `BaseGraphProps` its five properties. -/
theorem lemma_2_base_expander (t : ℕ) (ht : 1 ≤ t) :
    ∃ h₀ κ γ : ℝ, BaseConstants t h₀ γ κ ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∃ H : SimpleGraph (Fin n), BaseGraphProps h₀ γ κ H := by sorry

end ZeroExtensionGap
