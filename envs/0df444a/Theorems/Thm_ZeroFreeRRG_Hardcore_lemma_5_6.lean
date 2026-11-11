-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_6
-- name    : ZeroFreeRRG.Hardcore.lemma_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:38:45.654347+00:00
-- url     : https://prove2.me/theorems/8ae74c64-e163-4d71-bd9f-5fcd242c2b2e
-- title:
--   Lemma 5.6 — under Condition 1, Gibbs replicas have exponentially small planted probability of an atypical overlap
-- statement:
--   Fix $d\ge3$ and the hardcore model at $\alpha\in(0,1/2)$ or the $q$-state Potts model ($q\ge2$) at $\beta\in(0,1)$. Under Condition 1 at $(d,t)$, for every $\eta>0$ there exists $c>0$ such that for all sufficiently large $n$
--   $$\mathbb E_{\mathbb Q_n}\Big[\mu_G^{\otimes2}\big(\|\rho(\sigma,\sigma')-\pi\otimes\pi\|_\infty>\eta\big)\Big]\le e^{-cn},$$
--   where $\mathbb Q_n$ is the planted law (its graph marginal) and $(\sigma,\sigma')$ are two independent Gibbs replicas on $G$.
--
--   It controls the replica pairs outside the overlap box in the truncation Lemma 4.21.
--
--   Differences from the source:
--   - encoding: 'the hardcore model (Ω = {0,1}) or the antiferromagnetic Potts model (Ω = [q], q ≥ 2)' → one statement over m : Model with m.Valid (q ≥ 2 for Potts); spins Fin 2 (0 = unoccupied) and Fin q; reason: states both printed cases at once; each instance m = .hardcore, m = .potts q is the source's case
--   - encoding: CM_{n,d}: the multigraph of a uniform perfect matching of the dn labelled half-edges → the published AFIsingKS.Matching n d (fixed-point-free involutions of Fin n × Fin d) with cmE / cmProb; edges are matched pairs, so self-loops and parallel edges are kept; reason: same probability space; products over E(G) run over edge occurrences via one half-edge per pair
--   - encoding: limits and 'for all sufficiently large n' along admissible n (n ≥ d + 1, dn even) → filter atTop ⊓ 𝓟 {n | Even (n * d)}, resp. ∃ N, ∀ n ≥ N with Even (n * d); reason: n ≥ d + 1 holds eventually, so the two index sets agree for all large n
--   - encoding: O(·) and 'for all large n' → explicit existential constants C (and N) placed after the objects the page lets them depend on; reason: standard meaning of the asymptotic notation
--   - encoding: Pr_{ℚ_n}, E_{ℚ_n} with an independent reveal set U ∼ Bernoulli(s)^{⊗V} → finite sums plantedPinnedE over (pairing, σ, U) with weights ℚ_n(G, σ) · s^{|U|}(1 − s)^{n − |U|}; a probability is the expectation of an indicator; reason: the planted law and the reveal set are finitely supported
--   - encoding: ‖ρ(σ,σ′) − π⊗π‖_∞ > η → ∃ (a,b), η < |ρ_{ab}(σ,σ′) − π_a π_b|; reason: entrywise maximum norm
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 39, Lemma 5.6 (with the §5.2 standing assumptions)

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments

open scoped Classical

namespace ZeroFreeRRG.Hardcore

/-- **Lemma 5.6** (exponential overlap bound; p. 39), for `d ≥ 3` and the hardcore model at
`α ∈ (0, 1/2)` or the `q`-state Potts model (`q ≥ 2`) at `β ∈ (0, 1)`. Under Condition 1 at
`(d, t)`, for every `η > 0` there is `c > 0` such that for all sufficiently large admissible `n`,
`E_{ℚ_n}[µ_G^{⊗2}(‖ρ(σ, σ') − π ⊗ π‖_∞ > η)] ≤ e^{−cn}` (the expectation over the graph marginal
of the planted law). -/
theorem lemma_5_6 (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t) :
    ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
      plantedE m t d n (fun M _ => replicaProb m t M (fun σ σ' =>
          ∃ ab : m.Spin × m.Spin, η < |overlap σ σ' ab - m.pi t ab.1 * m.pi t ab.2|))
        ≤ Real.exp (-c * n) := by sorry

end ZeroFreeRRG.Hardcore
