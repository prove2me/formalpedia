-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_9_lifts
-- name    : ZeroExtensionGap.lemma_9_lifts
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:00.395475+00:00
-- url     : https://prove2.me/theorems/7123984b-da21-47f4-8554-103bcca63deb
-- title:
--   Lemma 9 — level-$i$ lifts form a large matching between children
-- statement:
--   Let $X_t,\dots,X_1$ be a valid expander tower with final graph $X=X_1$. Let $i\in[t]$, let $C$ be an $i$-cloud, let $\{u,v\}$ be an edge in the core of $X_i$ corresponding to $C$, and let $C_u,C_v$ be the corresponding children of $C$. The level-$i$ lifts of $\{u,v\}$ in $X$ form a matching $M$ between $C_u$ and $C_v$ with
--
--   $$|M|\ge\big(n-\lceil n^{0.99}\rceil\big)^{i-1}\ge n^{i-1}\Big(1-\frac{(t-1)\lceil n^{0.99}\rceil}{n}\Big).$$
--
--   Differences from the source:
--   - encoding: "sufficiently large even integer $n$" and $t$ fixed at the head of the section → binders `t`, `N₀ ≤ n`, `Even n`; reason: standing assumptions of the section, written out; no instance changes
--   - generalization: the constants of Lemma 2 and $\kappa_{\mathrm{tow}}$ of Lemma 7 → every admissible choice of these constants (`BaseConstants`, `0 < κtow`); reason: the paper's constants are one admissible choice, and the argument uses only the stated bounds, so the printed statement is an instance
--   - encoding: stage $X_i$ with vertex tuples $(x_t,\dots,x_i)$ → depth $j=t-i$, `towerGraph H g φ j` on the nested product `TowerV n j`; reason: a reindexing of the same tower
--   - encoding: the core of $X_i$ corresponding to $C$ → the image of $C$ under $\pi_i$, with $\{u,v\}$ adjacent in $X_i$; reason: $\pi_i$ maps an $i$-cloud onto the vertex set of its core (p.16)
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 9, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ZeroExtensionGap_towerGraph

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 9, p.19 (PDF p.21).
**Formalization Note.** The core of `X_i` corresponding to the `i`-cloud `C` is the image `π_i(C)`, so `u, v`
are vertices of that image adjacent in `X_i`. `C_u, C_v` are `cloudChild`. `n` sufficiently large and even is
standing. The cardinality bounds are in `ℝ`, and the subtraction is real. -/
theorem lemma_9_lifts (t : ℕ) (ht : 1 ≤ t) (h₀ γ κ κtow : ℝ) (hc : BaseConstants t h₀ γ κ)
    (hκtow : 0 < κtow) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∀ (H : SimpleGraph (Fin n)) (φ : Realization n), IsValidTower t h₀ γ κ κtow H φ →
      ∀ (i : ℕ) (hi : 1 ≤ i), i ≤ t →
      ∀ C : Finset (TowerV n (t - 1)), IsCloud t i C →
      ∀ u v : TowerV n (t - i), u ∈ C.image (piProj t i hi) → v ∈ C.image (piProj t i hi) →
        (towerGraph H (gOf γ n) φ (t - i)).Adj u v →
        IsMatchingBetween (levelLifts t H (gOf γ n) φ i hi u v)
          (cloudChild t i hi C u) (cloudChild t i hi C v) ∧
        ((n : ℝ) - (⌈(n : ℝ) ^ (0.99 : ℝ)⌉₊ : ℝ)) ^ (i - 1) ≤
          ((levelLifts t H (gOf γ n) φ i hi u v).card : ℝ) ∧
        (n : ℝ) ^ (i - 1) * (1 - ((t : ℝ) - 1) * (⌈(n : ℝ) ^ (0.99 : ℝ)⌉₊ : ℝ) / (n : ℝ)) ≤
          ((n : ℝ) - (⌈(n : ℝ) ^ (0.99 : ℝ)⌉₊ : ℝ)) ^ (i - 1) := by sorry

end ZeroExtensionGap
