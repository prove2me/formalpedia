-- Prove2me | Theorems.Thm_WinterExtrinsic_eq_B3_corrected
-- name    : WinterExtrinsic.eq_B3_corrected
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:09.406575+00:00
-- url     : https://prove2.me/theorems/020a3585-218e-46af-8c99-04b30c4dac4b
-- title:
--   Eq. (B3) — typical words are captured by the typical projector of the average state (corrected)
-- statement:
--   Let $\{\hat\rho_j, \lambda_j\}_{j=1}^m$ be an ensemble of density matrices on $\mathbb C^d$ with average $\rho = \sum_j \lambda_j \hat\rho_j$, and fix an eigenbasis $e_1, \dots, e_d$ of $\rho$ with eigenvalues $R_1, \dots, R_d$. For $\delta > 0$ let
--
--   $$\mathcal T^l_{\lambda,\delta} = \Big\{ j^l \in [m]^l : \forall j\ \ |N(j \mid j^l) - l\lambda_j| \le \delta \sqrt{l}\sqrt{\lambda_j(1-\lambda_j)} \Big\}$$
--
--   be the $\lambda$-typical words, $\Pi^l_{\rho,\delta'} = \sum_{t^l \in \mathcal T^l_{R,\delta'}} e_{t_1}\otimes\cdots\otimes e_{t_l}$ the typical projector of $\rho$, and $\hat\rho_{j^l} = \hat\rho_{j_1}\otimes\cdots\otimes\hat\rho_{j_l}$.
--
--   Then for every $\delta > 0$ and every $\eta > 0$ there exist $\delta' > 0$ and $L \in \mathbb N$ such that for all $l \ge L$ and all $j^l \in \mathcal T^l_{\lambda,\delta}$,
--
--   $$\mathrm{Tr}\big(\hat\rho_{j^l}\, \Pi^l_{\rho,\delta'}\big) \ge 1 - \eta .$$
--
--   This is the form of eq. (B3) used in the proof of Theorem 2, to show that the operators $\xi'_{j^l}$ keep most of their trace (eq. (10)). The printed (B3), $\mathrm{Tr}(\hat\rho_{j^l}\Pi^l_{\rho,\delta}) \ge 1 - m^2 d/\delta^2$ with the same $\delta$, is false.
--
--   **Formalization Note** The eigen-decomposition of $\rho$ is a `FineResolution d` `S` with `S.state` $= \rho$; `varianceProjector S l δ'` is $\Pi^l_{\rho,\delta'}$ and `varianceSet λ l δ` is $\mathcal T^l_{\lambda,\delta}$ (both from Winter's thesis layer `Renew46.P43`). $\lambda$ is a `PMF (Fin m)`.
--
--   Differences from the source:
--   - correction: $\mathrm{Tr}(\hat\rho_{j^l}\Pi^l_{\rho,\delta}) \ge 1 - m^2d/\delta^2$ for all $j^l$ → for every $\delta, \eta > 0$ some $\delta' > 0$ and $L$ give $\mathrm{Tr}(\hat\rho_{j^l}\Pi^l_{\rho,\delta'}) \ge 1-\eta$ for all $l \ge L$ and all $j^l \in \mathcal T^l_{\lambda,\delta}$; reason: the printed bound is false even for typical words (d = 2, m = 5, λ uniform, $\hat\rho_j = \mathrm{diag}(W_j, 1-W_j)$, W = (0.2, 0.9, 0.4, 0.1, 1.0), δ = 12, l = 300, a typical word with letter counts (3, 140, 5, 10, 142): the left side is 0.0017, the right side 0.653); this is the form the proof of Theorem 2 uses.
--   - reading: a collection of states $\hat\rho_j$ and a state $\rho$ (Appendix B) → an ensemble $\{\hat\rho_j, \lambda_j\}$ of density matrices with $\rho = \sum_j \lambda_j\hat\rho_j$; reason: Appendix B leaves the relation implicit, and in the proof of Theorem 2 (p.4) $\rho$ is the $\lambda$-average of the canonical ensemble; without the relation (B3) has no content.
--   - encoding: "fix eigenstates $e_1,\dots,e_d$" → a `FineResolution d` (eigenvalues and a unitary eigenbasis) whose `state` is $\rho$; $\lambda$ as a `PMF`; words as `Fin l → Fin m`; reason: Lean representation, same instances.
-- source:
--   Winter, "Extrinsic" and "intrinsic" data in quantum measurements, arXiv:quant-ph/0109050v3, Appendix B, eq. (B3), p.15 (definitions of T, Π on p.15; use in the proof of Theorem 2, eqs. (9)–(10), p.4)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

namespace WinterExtrinsic

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P43

/-- Eq. (B3), corrected: for every ensemble `{ρ̂_j, λ_j}` with average `ρ`, every `δ > 0` and
every `η > 0` there are `δ′ > 0` and `L` such that for all `l ≥ L` and every `λ`-typical word
`j^l ∈ T^l_{λ,δ}`, `Tr(ρ̂_{j^l} Π^l_{ρ,δ′}) ≥ 1 − η`.

Winter, *"Extrinsic" and "intrinsic" data in quantum measurements*, arXiv:quant-ph/0109050v3,
Appendix B, eq. (B3), p.15: "Tr(ρ̂_{j^l} Π^l_{ρ,δ}) ≥ 1 − m²d/δ²", used in the proof of
Theorem 2 (p.4, for (10)) only for `j^l ∈ T^l_{λ,δ}`.

**Correction.** The printed bound is false (d = 2, m = 5, λ uniform,
ρ̂_j = diag(W_j, 1 − W_j) with W = (0.2, 0.9, 0.4, 0.1, 1.0), δ = 12, l = 300, a typical word
with letter counts (3, 140, 5, 10, 142): the left side is 0.0017, the right side 0.653). This is
the form the proof of Theorem 2 needs.

**Formalization Note.** `S : FineResolution d` is a spectral decomposition of `ρ = S.state`
(eigenvalues `R_t` and eigenbasis `e_t`, "fix eigenstates e_1, …, e_d", p.15);
`varianceProjector S l δ′` is `Π^l_{ρ,δ′}` and `varianceSet λ l δ` is `T^l_{λ,δ}` (p.15).
`ρ̂_{j^l} = ρ̂_{j_1} ⊗ ⋯ ⊗ ρ̂_{j_l}` is `wordTensor`. The ensemble is any one with average `ρ`; the
canonical ensemble is a case of it. -/
theorem eq_B3_corrected {d m : ℕ} (S : FineResolution d) (lam : PMF (Fin m))
    (ρh : Fin m → Matrix (Fin d) (Fin d) ℂ) (hρh : ∀ j, IsDensityMatrix (ρh j))
    (havg : S.state = ∑ j, (((lam j).toReal : ℝ) : ℂ) • ρh j)
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∃ L : ℕ, ∀ l ≥ L, ∀ w ∈ varianceSet lam l δ,
      1 - η ≤ effectProb (varianceProjector S l δ') (wordTensor fun k => ρh (w k)) := by sorry

end WinterExtrinsic
