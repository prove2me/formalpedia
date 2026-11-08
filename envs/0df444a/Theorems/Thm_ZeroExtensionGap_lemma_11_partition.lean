-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_11_partition
-- name    : ZeroExtensionGap.lemma_11_partition
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:45.97904+00:00
-- url     : https://prove2.me/theorems/2ed65f2e-9a71-4c50-9e77-e361b0357d83
-- title:
--   Lemma 11 — random partitions of small sets in the final graph
-- statement:
--   There is a constant $K_t\ge1$ with the following property. For every fixed $0<\tau\le\tau_0=1/(200\log(20t))$ and every sufficiently large even integer $n$, let $X_t,\dots,X_1$ be a valid expander tower with an $n$-vertex base graph and final graph $X:=X_1$. For every $Z\subseteq V(X)$ with $|Z|\le n$ and every $2\le i\le t$, there is a $\tau\sigma_i$-bounded random partition $P$ of $Z$, with respect to $d_X$, such that
--
--   $$\Pr[P(x)\ne P(y)]\le K_t\frac{d_X(x,y)}{\sigma_{i-1}}$$
--
--   for every $x,y\in Z$. $K_t$ depends only on $t$, and the lower bound on $n$ may also depend on $\tau$.
--
--   Differences from the source:
--   - encoding: "sufficiently large even integer $n$" and $t$ fixed at the head of the section → binders `t`, `N₀ ≤ n`, `Even n`; reason: standing assumptions of the section, written out; no instance changes
--   - generalization: the constants of Lemma 2 and $\kappa_{\mathrm{tow}}$ of Lemma 7 → every admissible choice of these constants (`BaseConstants`, `0 < κtow`); reason: the paper's constants are one admissible choice, and the argument uses only the stated bounds, so the printed statement is an instance
--   - encoding: stage $X_i$ with vertex tuples $(x_t,\dots,x_i)$ → depth $j=t-i$, `towerGraph H g φ j` on the nested product `TowerV n j`; reason: a reindexing of the same tower
--   - encoding: a random partition → its law, `PMF (Finpartition _)`; reason: partitions of a finite set form a finite type, whatever process generated them
--   - encoding: shortest-path distance $d$ with values in $[0,\infty]$ → `ℝ≥0∞`, with `toReal` under connectivity; reason: on connected pairs the real value is the distance; there is no junk value
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 11, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_ZeroExtensionGap_towerGraph
import Definitions.Def_ZeroExtensionGap_RandomPartition

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 11, p.21 (PDF p.23).
**Formalization Note.** `K` depends only on `t` and the constants of Lemmas 2 and 7, so it precedes `τ`; the
lower bound `N₀` on `n` may depend on `τ` (p.21, PDF p.23). `d_X` is the ambient distance of the final graph, so
shortest paths may leave `Z`. `t ≥ 2` is the standing assumption of §5. -/
theorem lemma_11_partition (t : ℕ) (ht : 2 ≤ t) (h₀ γ κ κtow : ℝ) (hc : BaseConstants t h₀ γ κ)
    (hκtow : 0 < κtow) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ τ : ℝ, 0 < τ → τ ≤ tau0 t → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∀ (H : SimpleGraph (Fin n)) (φ : Realization n), IsValidTower t h₀ γ κ κtow H φ →
      ∀ Z : Finset (TowerV n (t - 1)), Z.card ≤ n →
      ∀ i : ℕ, 2 ≤ i → i ≤ t →
        ∃ P : PMF (Finpartition Z),
          IsBoundedRandomPartition (towerDist t H (gOf γ n) φ (t - 1)) (τ * sigma t n i) P ∧
          ∀ x ∈ Z, ∀ y ∈ Z,
            separationProb P x y ≤
              K * (towerDist t H (gOf γ n) φ (t - 1) x y).toReal / sigma t n (i - 1) := by sorry

end ZeroExtensionGap
