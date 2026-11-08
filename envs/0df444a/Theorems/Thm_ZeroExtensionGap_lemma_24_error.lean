-- Prove2me | Theorems.Thm_ZeroExtensionGap_lemma_24_error
-- name    : ZeroExtensionGap.lemma_24_error
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:06.196007+00:00
-- url     : https://prove2.me/theorems/d7b069f0-4a1c-44e0-a117-b70bb2a2b5d9
-- title:
--   Lemma 24 — the top-level error of the representatives
-- statement:
--   There is a constant $C_t\ge1$, independent of $c$, $\tau$ and $n$, such that, if $\Phi(f)<cN\rho$, then the representatives constructed in §6.1–§6.2 satisfy
--
--   $$e_t\le C_t(c+\tau+L_n),$$
--
--   where $L_n=(t-1)\lceil n^{0.99}\rceil/n$. Here $f:V(X)\to V(X)$ is the labelling of a valid tower's final graph, $\Phi$ its cost (3), and $e_t$ the fraction of vertices whose label is farther than $r_t$ from the representative of $V(X)$.
--
--   Differences from the source:
--   - encoding: "sufficiently large even integer $n$" and $t$ fixed at the head of the section → binders `t`, `N₀ ≤ n`, `Even n`; reason: standing assumptions of the section, written out; no instance changes
--   - generalization: the constants of Lemma 2 and $\kappa_{\mathrm{tow}}$ of Lemma 7 → every admissible choice of these constants (`BaseConstants`, `0 < κtow`); reason: the paper's constants are one admissible choice, and the argument uses only the stated bounds, so the printed statement is an instance
--   - encoding: stage $X_i$ with vertex tuples $(x_t,\dots,x_i)$ → depth $j=t-i$, `towerGraph H g φ j` on the nested product `TowerV n j`; reason: a reindexing of the same tower
--   - encoding: a random partition → its law, `PMF (Finpartition _)`; reason: partitions of a finite set form a finite type, whatever process generated them
--   - generalization: $n$ "sufficiently large", fixed in §6.1 before $c$ is chosen in §6.3 → `N₀` chosen before `c` (`∀ c > 0` comes after `n`, the tower and `f`); reason: the proof's only largeness step involving $c$ is $\rho\ell_i/\sigma_{i-1}=(\log n)^{-1/(t+1)}\le1$, which does not depend on $c$; for each fixed $c$ the Lean statement gives the printed one
--   - reading: "the representatives constructed above", from a construction with free choices → such a family exists, and the bound holds for every such family (`IsRepresentativeFamily`); reason: the strongest reading, and the one the printed proof gives; $K$ is the constant of Lemma 11
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 24, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_ZeroExtensionGap_IsRepresentativeFamily

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Lemma 24, p.31 (PDF p.33).
**Formalization Note.** "The representatives constructed above" comes from a construction with free choices
(§6.1–§6.2, pp.29–30, PDF pp.31–32), which `IsRepresentativeFamily` records. The reading stated is the strongest:
such a family exists, and the bound holds for every such family. `K` is the constant of Lemma 11 used in the
construction. `C_t` is independent of `c`, `τ` and `n`; `N₀` is independent of `c`, and may depend on `τ`. -/
theorem lemma_24_error (t : ℕ) (ht : 2 ≤ t) (h₀ γ κ κtow : ℝ) (hc : BaseConstants t h₀ γ κ)
    (hκtow : 0 < κtow) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ Ct : ℝ, 1 ≤ Ct ∧ ∀ τ : ℝ, 0 < τ → τ ≤ tau0 t →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∀ (H : SimpleGraph (Fin n)) (φ : Realization n), IsValidTower t h₀ γ κ κtow H φ →
      ∀ f : TowerV n (t - 1) → TowerV n (t - 1),
        (∃ z, IsRepresentativeFamily t H (gOf γ n) φ τ K f z) ∧
        ∀ c : ℝ, 0 < c → Phi t H (gOf γ n) φ f < c * (n : ℝ) ^ t * rho t n →
          ∀ z, IsRepresentativeFamily t H (gOf γ n) φ τ K f z →
            levelError t H (gOf γ n) φ τ f z t ≤ Ct * (c + τ + Ln t n) := by sorry

end ZeroExtensionGap
