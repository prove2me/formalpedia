-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_2_5
-- name    : Z2PostSamp.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:27.1032+00:00
-- url     : https://prove2.me/theorems/25787575-d3a4-496f-adc7-37036d5f2e47
-- title:
--   Lemma 2.5 — optimization accuracy of the projected-gradient routine under the prescribed tolerances: $\Phi_k(\widehat m^{(k)})-\min_{\mathcal K_k}\Phi_k\le n^{-12}$
-- statement:
--   Fix $\lambda>1$. For all sufficiently large $n$ the following holds. Let $J$ be symmetric with $\|J\|_F\le n^2$, let $k<n$ and fix a prefix $x_{S_k}$. Let $K$ be a nonempty compact convex set of vectors on $R_k$ inside the clipped cube $D_{R_k,n}=[-c_n,c_n]^{R_k}$ with diameter at most $D_n=2\sqrt n$, on which $\Phi_k(\cdot;x_{S_k})$ is convex. Put
--
--   $$B_n=\sqrt n\{n^2+1+2\|J\|_F+\lambda^2\},\qquad L_n=\lceil n^{40}\rceil,\qquad\gamma_n=\frac{D_n}{B_n\sqrt{L_n}},$$
--
--   and let $u^0\in K$ and $g^t$, $u^{t+1}$ ($t<L_n$) satisfy the prescribed precision and feasibility rules
--
--   $$\|g^t-\nabla_u\Phi_k(u^t;x_{S_k})\|\le n^{-100},\qquad u^{t+1}\in K,\qquad\big\|u^{t+1}-\mathrm{Proj}_K(u^t-\gamma_ng^t)\big\|\le n^{-100}.$$
--
--   Then the average of the pre-update iterates $\widehat m=\frac1{L_n}\sum_{t<L_n}u^t$ satisfies
--
--   $$\Phi_k(\widehat m;x_{S_k})-\min_{u\in K}\Phi_k(u;x_{S_k})\le n^{-12}.\tag{2.16}$$
--
--   Each domain $\mathcal K_k(x_{S_k})$ is such a $K$, and Algorithm 2 (TAPOptimize) is such a run, so this is the accuracy guarantee of the sampler's optimization step. The exact-arithmetic step of the proof is the projected subgradient theorem (Bubeck, Theorem 3.2, referenced item).
--
--   **Formalization Note** Vectors are `EuclideanSpace ℝ (Fin n)` vanishing off $R_k$; $\mathrm{Proj}_K$ is the published argmin predicate `IsEuclideanProj`. The minimum is written as the bound against every $v\in K$ (it is attained on the compact $K$). "For all sufficiently large $n$" is $\exists N_0\,\forall n\ge N_0$ with $N_0$ depending on $\lambda$ only.
--
--   Differences from the source:
--   - generalization: Algorithm 2 run on 𝒦_k(x_{S_k}) from the restricted stored centre, returning a vector satisfying the prescribed precision and feasibility rules → every nonempty compact convex K ⊆ D_{R_k,n} of diameter ≤ D_n, every start u⁰ ∈ K and every run meeting the three tolerances of §3.3, and every k < n; reason: each 𝒦_k is such a K (p.25) and Algorithm 2's run is such a run; exact Algorithm 2 is the zero-error case
--   - reading: J (the model's interaction matrix) → hypothesis J symmetric; reason: J = λY/√n with Y symmetric is the standing setting; for symmetric J the gradient formula of Algorithm 2 is ∇Φ_k
--   - encoding: min_{u∈𝒦_k} Φ_k(u) → the bound Φ_k(m̂) − Φ_k(v) ≤ n^{−12} for every v ∈ K; reason: the minimum of the continuous Φ_k on the compact K is attained
--   - encoding: for all sufficiently large n → ∃ N₀ ∀ n ≥ N₀, N₀ depending on λ; reason: definition
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 2.5, p.12, (2.16); Algorithm 2, p.12; §3.3, p.25 (tolerances)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_RevealPath
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_TAP
import Definitions.Def_Z2PostSamp_Construction
import Definitions.Def_BubeckCO_PSGD_IsEuclideanProj

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix BubeckCO.PSGD

namespace Z2PostSamp

/-- **Lemma 2.5 (optimization accuracy), under the prescribed tolerances of §3.3.**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 2.5, p.12: "Suppose that `‖J‖_F ≤ n²` and `Φ_k(·; x_{S_k})` is convex on `𝒦_k(x_{S_k})`.
Assume that Algorithm 2 returns a vector satisfying the prescribed precision and feasibility rules.
Then, for all sufficiently large `n`, `Φ_k(m̂^{(k)}(x_{S_k}); x_{S_k}) − min_{u∈𝒦_k(x_{S_k})} Φ_k(u; x_{S_k})
≤ n^{−12}` (2.16)." Algorithm 2 (p.12): `L_n = ⌈n^{40}⌉` iterations, `γ_n = D_n/(B_n√L_n)`,
`B_n = √n{n² + 1 + 2‖J‖_F + λ²}`, `D_n = 2√n`, `u^{t+1} = Proj_{𝒦_k}(u^t − γ_n g)`, output the
average of the pre-update iterates. The prescribed rules (§3.3, p.25):
`‖g^t − ∇_uΦ_k(u^t; x_{S_k})‖ ≤ n^{−100}`, `u^{t+1} ∈ 𝒦_k(x_{S_k})`,
`‖u^{t+1} − Proj_{𝒦_k(x_{S_k})}(u^t − γ_n g^t)‖ ≤ n^{−100}`; every `𝒦_k` lies in `D_{R_k,n}` and has
diameter at most `D_n` (p.25).

**Formalization Note.** Stated for every compact convex nonempty `K` inside the clipped cube
`D_{R_k,n}` with diameter at most `D_n` (each `𝒦_k(x_{S_k})` is one, p.25), every start `u^0 ∈ K` (the
paper starts at the restricted stored centre) and every run meeting the three tolerances; the exact
Algorithm 2 is the case of zero errors. Vectors are `EuclideanSpace ℝ (Fin n)` vanishing off `R_k`;
`Proj_K` is the published argmin predicate `IsEuclideanProj`. `J` is symmetric (the model's `J` always
is; for symmetric `J`, `tapGrad` is the gradient of `Φ_k`). "For all sufficiently large `n`" is
`∃ N₀, ∀ n ≥ N₀`, with `N₀` depending on `λ` only. `min_K Φ_k` is written as the bound against every
`v ∈ K` (the minimum is attained on the compact `K`). -/
theorem lemma_2_5 (lam : ℝ) (hlam : 1 < lam) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ J : Matrix (Fin n) (Fin n) ℝ, J.IsSymm →
      frobNorm J ≤ (n : ℝ) ^ 2 → ∀ (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ), k < n →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), K.Nonempty → IsCompact K → Convex ℝ K →
      (∀ u ∈ K, (∀ i, i ∉ Rset I k → u i = 0) ∧ ∀ i ∈ Rset I k, |u i| ≤ cn n) →
      (∀ u ∈ K, ∀ w ∈ K, ‖u - w‖ ≤ 2 * Real.sqrt n) →
      ConvexOn ℝ K (fun u => tapObj lam J I x k (WithLp.ofLp u)) →
      ∀ u g : ℕ → EuclideanSpace ℝ (Fin n), u 0 ∈ K →
      (∀ t < ⌈(n : ℝ) ^ 40⌉₊,
        ‖g t - WithLp.toLp 2 (tapGrad lam J I x k (WithLp.ofLp (u t)))‖ ≤ (n : ℝ) ^ (-100 : ℤ) ∧
        u (t + 1) ∈ K ∧
        ∃ p, IsEuclideanProj K (u t - (2 * Real.sqrt n /
            (Real.sqrt n * ((n : ℝ) ^ 2 + 1 + 2 * frobNorm J + lam ^ 2) *
              Real.sqrt ⌈(n : ℝ) ^ 40⌉₊)) • g t) p ∧
          ‖u (t + 1) - p‖ ≤ (n : ℝ) ^ (-100 : ℤ)) →
      ∀ v ∈ K, tapObj lam J I x k (WithLp.ofLp ((1 / (⌈(n : ℝ) ^ 40⌉₊ : ℝ)) •
          ∑ t ∈ Finset.range ⌈(n : ℝ) ^ 40⌉₊, u t)) - tapObj lam J I x k (WithLp.ofLp v)
        ≤ (n : ℝ) ^ (-12 : ℤ) := by sorry

end Z2PostSamp
