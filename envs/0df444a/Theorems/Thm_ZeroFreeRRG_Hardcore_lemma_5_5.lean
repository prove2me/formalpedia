-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_5
-- name    : ZeroFreeRRG.Hardcore.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:38:45.092202+00:00
-- url     : https://prove2.me/theorems/cd2328ba-c403-4af9-83ae-9e3f6d067389
-- title:
--   Lemma 5.5 — local moments converge to holomorphic limits, local paired rate function is negative definite, cycle counts and (39), ∑λ_ℓ sup|δ_ℓ|² < ∞
-- statement:
--   Fix $d\ge3$ and the hardcore or $q$-state Potts model ($q\ge2$); expectations are under $\mathrm{CM}_{n,d}$. Assume $t$ is nontrivial, $\kappa_a(t)\le0$ for all $a\ge2$, and Condition 2 holds at $t$. For every sufficiently small open overlap box $B$ around $\pi(t)\otimes\pi(t)$ there exist $c>0$ and an open disk $D_0$ about $t$ such that:
--   (1) $a_n(z)$ and $\mathbb E[\mathcal Z^{(2)}_{G,B}(z,w)]/[a_n(z)a_n(w)]$ converge locally uniformly on $D_0$ and $D_0\times D_0$ to holomorphic functions, the limit of $a_n$ nowhere zero on $D_0$;
--   (2) for real $s,u\in D_0$ with $P(s),P(u)\ge0$ and every edge marginal $Q$ with vertex marginal $\rho\in B$, $\Phi_{s,u}(\rho,Q)\le-c(\|\rho-\pi(s)\otimes\pi(u)\|_2^2+\|Q-P(s)\otimes P(u)\|_F^2)$;
--   (3) for every $m\ge1$, $(X_{1,n},\dots,X_{m,n})\to_d(Z_1,\dots,Z_m)$ with independent $Z_\ell\sim\mathrm{Poisson}(\lambda_\ell)$, and for real $s\in D_0$ with $P(s)\ge0$ and $j_1,\dots,j_m\ge0$,
--   $$\frac{\mathbb E[\mathcal Z^{(2)}_{G,B}(s,s)]}{a_n(s)^2}\to\exp\Big(\sum_{\ell\ge1}\lambda_\ell\delta_\ell(s)^2\Big),\qquad \frac{\mathbb E[\mathcal Z_G(s)\prod_\ell(X_{\ell,n})_{j_\ell}]}{a_n(s)}\to\prod_\ell\big(\lambda_\ell(1+\delta_\ell(s))\big)^{j_\ell};$$
--   (4) $\sum_{\ell\ge1}\lambda_\ell\sup_{z\in D_0}|\delta_\ell(z)|^2<\infty$ and $1+\delta_\ell(z)\neq0$ for all $\ell\ge3$, $z\in D_0$.
--
--   These verify (B1)–(B5) for Theorem 3.2.
--
--   Differences from the source:
--   - encoding: 'the hardcore model (Ω = {0,1}) or the antiferromagnetic Potts model (Ω = [q], q ≥ 2)' → one statement over m : Model with m.Valid (q ≥ 2 for Potts); spins Fin 2 (0 = unoccupied) and Fin q; reason: states both printed cases at once; each instance m = .hardcore, m = .potts q is the source's case
--   - encoding: CM_{n,d}: the multigraph of a uniform perfect matching of the dn labelled half-edges → the published AFIsingKS.Matching n d (fixed-point-free involutions of Fin n × Fin d) with cmE / cmProb; edges are matched pairs, so self-loops and parallel edges are kept; reason: same probability space; products over E(G) run over edge occurrences via one half-edge per pair
--   - encoding: limits and 'for all sufficiently large n' along admissible n (n ≥ d + 1, dn even) → filter atTop ⊓ 𝓟 {n | Even (n * d)}, resp. ∃ N, ∀ n ≥ N with Even (n * d); reason: n ≥ d + 1 holds eventually, so the two index sets agree for all large n
--   - reading: 'for every sufficiently small (open) overlap box B around π(t) ⊗ π(t)'; a box is the preimage of an open axis-aligned box in |Ω|² − 1 coordinates of Δ_{Ω×Ω} → ∃ r > 0 such that for every dropped coordinate c₀ and corners lo, hi with π(t)⊗π(t) ∈ overlapBox c₀ lo hi and all side lengths hi − lo < r, the conclusion holds; reason: 'sufficiently small' = below some size every such box works; every choice of the dropped coordinate is covered (the stronger reading)
--   - encoding: an open (complex) disk D₀ about t → Metric.ball (t : ℂ) R with R > 0; reason: same set
--   - encoding: nonconstant eigenvalues κ_2(t), …, κ_|Ω|(t) of K_t counted with algebraic multiplicity → the set m.nonconstEig t of eigenvalues of K_t on {f : π(t)ᵀ f = 0}; reason: only max_a |κ_a| and the signs κ_a ≤ 0 are used; these depend only on the set of values
--   - encoding: κ_a(t) ≤ 0 (real at real t) → κ ≤ 0 in the order of ℂ (scoped ComplexOrder): real and nonpositive; reason: the eigenvalues are real at real t (reversibility, p. 15), so this is the same condition
--   - encoding: D_KL with 0 log(0/q) = 0, p log(p/0) = +∞; Φ_s may equal −∞ → klDiv, rateFn valued in EReal (⊥ = −∞); reason: D_KL(ρ‖π(s)) is finite because π(s) > 0, so no ⊤ − ⊤ occurs
--   - encoding: convergence locally uniformly on D₀ × D₀ to a holomorphic function of (z, w) → TendstoLocallyUniformlyOn on ball ×ˢ ball to G2 with DifferentiableOn ℂ G2 on the product; reason: holomorphic in two variables = complex differentiable on the open product set
--   - encoding: (X_{1,n}, …, X_{m,n}) →d independent Poisson(λ_ℓ) → cmProb(X_{ℓ,n} = j_ℓ for ℓ ≤ m) → ∏_ℓ Poisson(λ_ℓ)({j_ℓ}); reason: for ℕ^m-valued vectors convergence in distribution is convergence of point probabilities; the limit law is the product of Poisson laws
--   - encoding: ∑_{ℓ ≥ 1} λ_ℓ sup_{z ∈ D₀} |δ_ℓ(z)|² < ∞ → ∃ β with |δ_{ℓ}(z)|² ≤ β_ℓ on D₀ and ∑ λ_ℓ β_ℓ summable; reason: equivalent (take β_ℓ the supremum)
--   - encoding: ∑_{ℓ ≥ 1} and products over ℓ = 1..m → tsum over ℓ + 1 (ℓ ∈ ℕ) and products over i : Fin m of index i + 1; reason: index shift
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), pp. 39, Lemma 5.5 (with Definition 5.4, eqs. (30), (38), (39), and the §5.1 standing assumptions)

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments

open scoped Classical ComplexOrder
open Filter Topology AFIsingKS

namespace ZeroFreeRRG.Hardcore

/-- **Lemma 5.5** (local moments and short-cycle estimates; p. 39), for `d ≥ 3` and the hardcore or
`q`-state Potts model (`q ≥ 2`), under `CM_{n,d}` along admissible `n`. Let `t` be nontrivial with
`κ_a(t) ≤ 0` for all `a ≥ 2` and Condition 2 at `t`. There is a size `r > 0` such that for every
open overlap box `B` around `π(t) ⊗ π(t)` with all side lengths `< r` there exist `c > 0` and an open
disk `D₀` about `t` with:
(1) `a_n(z)` and `E[𝒵^{(2)}_{G,B}(z, w)]/[a_n(z)a_n(w)]` converge locally uniformly on `D₀` and
`D₀ × D₀` to holomorphic functions, the limit of `a_n` nowhere zero on `D₀`;
(2) for all real `s, u ∈ D₀` with `P(s), P(u) ≥ 0` and every edge marginal `Q` on `Ω × Ω` with vertex
marginal `ρ ∈ B`, `Φ_{s,u}(ρ, Q) ≤ −c(‖ρ − π(s) ⊗ π(u)‖₂² + ‖Q − P(s) ⊗ P(u)‖_F²)`;
(3) for every `k ≥ 1`, `(X_{1,n}, …, X_{k,n}) →d (Z_1, …, Z_k)` with independent
`Z_ℓ ∼ Poisson(λ_ℓ)`, and for every real `s ∈ D₀` with `P(s) ≥ 0` and `j_1, …, j_k ≥ 0`, (39):
`E[𝒵^{(2)}_{G,B}(s, s)]/a_n(s)² → exp(∑_{ℓ ≥ 1} λ_ℓ δ_ℓ(s)²)` and
`E[𝒵_G(s) ∏_ℓ (X_{ℓ,n})_{j_ℓ}]/a_n(s) → ∏_ℓ (λ_ℓ(1 + δ_ℓ(s)))^{j_ℓ}`;
(4) `∑_{ℓ ≥ 1} λ_ℓ sup_{z ∈ D₀} |δ_ℓ(z)|² < ∞`, and `1 + δ_ℓ(z) ≠ 0` for all `ℓ ≥ 3`, `z ∈ D₀`. -/
theorem lemma_5_5 (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.Nontrivial t)
    (hκ : ∀ κ ∈ m.nonconstEig (t : ℂ), κ ≤ 0) (hC2 : Condition2 m d t) :
    ∃ r : ℝ, 0 < r ∧ ∀ (c₀ : m.Spin × m.Spin) (lo hi : m.Spin × m.Spin → ℝ),
      tensorVec (m.pi t) (m.pi t) ∈ overlapBox c₀ lo hi → (∀ ab, hi ab - lo ab < r) →
      ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧
        -- (1)
        (∃ A : ℂ → ℂ, DifferentiableOn ℂ A (Metric.ball (t : ℂ) R) ∧
            (∀ z ∈ Metric.ball (t : ℂ) R, A z ≠ 0) ∧
            TendstoLocallyUniformlyOn (fun n z => an m d n z) A
              (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (Metric.ball (t : ℂ) R)) ∧
        (∃ G2 : ℂ × ℂ → ℂ,
            DifferentiableOn ℂ G2 (Metric.ball (t : ℂ) R ×ˢ Metric.ball (t : ℂ) R) ∧
            TendstoLocallyUniformlyOn
              (fun n (p : ℂ × ℂ) => cmE (fun M : Matching n d => Z2 m (overlapBox c₀ lo hi) p.1 p.2 M) /
                (an m d n p.1 * an m d n p.2)) G2
              (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
              (Metric.ball (t : ℂ) R ×ˢ Metric.ball (t : ℂ) R)) ∧
        -- (2)
        (∀ s u : ℝ, (s : ℂ) ∈ Metric.ball (t : ℂ) R → (u : ℂ) ∈ Metric.ball (t : ℂ) R →
          (∀ i j, 0 ≤ m.P s i j) → (∀ i j, 0 ≤ m.P u i j) →
          ∀ (ρ : m.Spin × m.Spin → ℝ) (Q : m.Spin × m.Spin → m.Spin × m.Spin → ℝ),
            IsEdgeMarginal ρ Q → ρ ∈ overlapBox c₀ lo hi →
            rateFn d (tensorVec (m.pi s) (m.pi u)) (tensorMat (m.P s) (m.P u)) ρ Q ≤
              (((-c) * sqDist ρ (tensorVec (m.pi s) (m.pi u)) Q (tensorMat (m.P s) (m.P u)) : ℝ)
                : EReal)) ∧
        -- (3)
        (∀ k : ℕ, 1 ≤ k → ∀ j : Fin k → ℕ,
          Tendsto (fun n => cmProb (fun M : Matching n d => ∀ i : Fin k, cycleCount M ((i : ℕ) + 1) = j i))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
            (𝓝 (∏ i : Fin k, (ProbabilityTheory.poissonMeasure (lamCyc d ((i : ℕ) + 1)).toNNReal).real {j i}))) ∧
        (∀ s : ℝ, (s : ℂ) ∈ Metric.ball (t : ℂ) R → (∀ i j, 0 ≤ m.P s i j) →
          Tendsto (fun n => cmE (fun M : Matching n d => Z2 m (overlapBox c₀ lo hi) s s M) /
              an m d n (s : ℂ) ^ 2)
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
            (𝓝 (Complex.exp (∑' ℓ : ℕ, (lamCyc d (ℓ + 1) : ℂ) * deltaCyc m (ℓ + 1) s ^ 2))) ∧
          ∀ k : ℕ, 1 ≤ k → ∀ j : Fin k → ℕ,
            Tendsto (fun n => cmE (fun M : Matching n d => normZ m (s : ℂ) M *
                ∏ i : Fin k, (((cycleCount M ((i : ℕ) + 1)).descFactorial (j i) : ℕ) : ℂ)) /
                an m d n (s : ℂ))
              (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
              (𝓝 (∏ i : Fin k, ((lamCyc d ((i : ℕ) + 1) : ℂ) * (1 + deltaCyc m ((i : ℕ) + 1) s)) ^ (j i)))) ∧
        -- (4)
        (∃ β : ℕ → ℝ, (∀ ℓ, ∀ z ∈ Metric.ball (t : ℂ) R, ‖deltaCyc m (ℓ + 1) z‖ ^ 2 ≤ β ℓ) ∧
            Summable (fun ℓ => lamCyc d (ℓ + 1) * β ℓ)) ∧
        (∀ ℓ : ℕ, 3 ≤ ℓ → ∀ z ∈ Metric.ball (t : ℂ) R, 1 + deltaCyc m ℓ z ≠ 0) := by sorry

end ZeroFreeRRG.Hardcore
