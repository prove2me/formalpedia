-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20
-- name    : ZeroFreeRRG.Hardcore.lemma_4_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:39:12.608194+00:00
-- url     : https://prove2.me/theorems/8634e0b6-fb44-42cc-9416-a0424ca17fb4
-- title:
--   Lemma 4.20 — |log a_n(t)| = O(log n), exponential upper tail of the pinned log-likelihood, and the pinned Bethe bound (29)
-- statement:
--   Fix $d\ge3$ and the hardcore model at $\alpha\in(0,1/2)$ or the $q$-state Potts model ($q\ge2$) at $\beta\in(0,1)$; $\mathrm{CM}=\mathrm{CM}_{n,d}$, $a_n(t)=\mathbb E_{\mathrm{CM}}[\mathcal Z_G(t)]$, $\mathbb Q_n$ the planted law, $U$ an independent Bernoulli($s$) reveal set and $\ell_s$ the pinned log-likelihood. Then $|\log a_n(t)|=O(\log(n+1))$. Moreover, for every $s\in[0,1]$ and $b>0$ there is $c>0$ with $\Pr_{\mathbb Q_n}[\ell_s-\mathbb E_{\mathbb Q_n}[\ell_s]>bn]\le e^{-cn}$ for all large $n$, and
--   $$\limsup_{n}\tfrac1n\mathbb E_{\mathbb Q_n}[\ell_s]\le\limsup_n\tfrac1n\mathbb E_{\mathbb Q_n}[\log\mathcal Z_G+\ell_s]\le\max_{\nu\in\mathcal P_\pi}\Big\{\mathcal B_{d,t}(\nu)+ds\,\mathbb E_\nu\Big[\sum_a\pi_a((M\mu)_a-1)^2\Big]\Big\}.\tag{29}$$
--
--   It feeds the planted overlap bound, Lemma 5.6.
--
--   Differences from the source:
--   - encoding: 'the hardcore model (Ω = {0,1}) or the antiferromagnetic Potts model (Ω = [q], q ≥ 2)' → one statement over m : Model with m.Valid (q ≥ 2 for Potts); spins Fin 2 (0 = unoccupied) and Fin q; reason: states both printed cases at once; each instance m = .hardcore, m = .potts q is the source's case
--   - encoding: CM_{n,d}: the multigraph of a uniform perfect matching of the dn labelled half-edges → the published AFIsingKS.Matching n d (fixed-point-free involutions of Fin n × Fin d) with cmE / cmProb; edges are matched pairs, so self-loops and parallel edges are kept; reason: same probability space; products over E(G) run over edge occurrences via one half-edge per pair
--   - encoding: limits and 'for all sufficiently large n' along admissible n (n ≥ d + 1, dn even) → filter atTop ⊓ 𝓟 {n | Even (n * d)}, resp. ∃ N, ∀ n ≥ N with Even (n * d); reason: n ≥ d + 1 holds eventually, so the two index sets agree for all large n
--   - encoding: O(·) and 'for all large n' → explicit existential constants C (and N) placed after the objects the page lets them depend on; reason: standard meaning of the asymptotic notation
--   - encoding: Pr_{ℚ_n}, E_{ℚ_n} with an independent reveal set U ∼ Bernoulli(s)^{⊗V} → finite sums plantedPinnedE over (pairing, σ, U) with weights ℚ_n(G, σ) · s^{|U|}(1 − s)^{n − |U|}; a probability is the expectation of an indicator; reason: the planted law and the reveal set are finitely supported
--   - encoding: lim sup_{n→∞} of real sequences → Filter.limsup of the EReal coercion along admissible n; reason: EReal is a complete lattice, so the limsup is the extended-real one with no junk value
--   - encoding: max_{ν ∈ 𝒫_π}{…} → ∃ ν₀ ∈ 𝒫_π maximizing the functional, and the bound by its value at ν₀; reason: 'max' asserts the maximum is attained
--   - encoding: α_RSB(d) = inf S_d with inf ∅ = 1/2 (32); 𝒫_π all Borel probability measures on Δ_Ω with mean π → alphaRSB d = if S d = ∅ then 1/2 else sInf (S d); cavityLaws: ProbabilityMeasure on ℝ^Ω null off stdSimplex, coordinatewise mean π; reason: Lean's sInf ∅ = 0 is overridden; S_d ⊆ (0, 1/2) is bounded below
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 31, Lemma 4.20 (with Definition 4.19 and the §4.3 standing assumptions, p. 31)

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments

open scoped Classical
open Filter MeasureTheory AFIsingKS

namespace ZeroFreeRRG.Hardcore

/-- **Lemma 4.20** (p. 31), for `d ≥ 3` and the hardcore model at `α ∈ (0, 1/2)` or the `q`-state
Potts model (`q ≥ 2`) at `β ∈ (0, 1)`, under `CM_{n,d}` along admissible `n`, with the planted law
`ℚ_n`, an independent Bernoulli(`s`) reveal set `U` and the pinned log-likelihood `ℓ_s`:
`|log a_n(t)| = O(log(n + 1))`; for every `s ∈ [0, 1]` and `b > 0` there is `c > 0` with
`Pr_{ℚ_n}[ℓ_s − E_{ℚ_n}[ℓ_s] > bn] ≤ e^{−cn}` for all large `n`; and (29)
`limsup (1/n) E_{ℚ_n}[ℓ_s] ≤ limsup (1/n) E_{ℚ_n}[log 𝒵_G + ℓ_s]
  ≤ max_{ν ∈ 𝒫_π} {B_{d,t}(ν) + ds E_ν[∑_a π_a((Mµ)_a − 1)²]}`, the maximum being attained. -/
theorem lemma_4_20 (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t) :
    (∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
        |Real.log (an m d n t)| ≤ C * Real.log (n + 1)) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ b : ℝ, 0 < b → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
        plantedPinnedE m t s d n (fun M σ U =>
            if pinnedLL m t M σ U - plantedPinnedE m t s d n (fun M' σ' U' => pinnedLL m t M' σ' U')
                > b * n then 1 else 0) ≤ Real.exp (-c * n)) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∃ ν₀ ∈ cavityLaws m t,
        (∀ ν ∈ cavityLaws m t,
          betheK m t d ν + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν : Measure (m.Spin → ℝ)) ≤
          betheK m t d ν₀ + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν₀ : Measure (m.Spin → ℝ))) ∧
        limsup (fun n : ℕ => (((1 : ℝ) / n *
            plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) : ℝ) : EReal))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) ≤
          limsup (fun n : ℕ => (((1 : ℝ) / n *
            plantedPinnedE m t s d n (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U)
              : ℝ) : EReal))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) ∧
        limsup (fun n : ℕ => (((1 : ℝ) / n *
            plantedPinnedE m t s d n (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U)
              : ℝ) : EReal))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) ≤
          ((betheK m t d ν₀ + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν₀ : Measure (m.Spin → ℝ)) : ℝ) : EReal)) := by sorry

end ZeroFreeRRG.Hardcore
