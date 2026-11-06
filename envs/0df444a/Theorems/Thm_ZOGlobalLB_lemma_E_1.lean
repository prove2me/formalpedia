-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_E_1
-- name    : ZOGlobalLB.lemma_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:51:39.426605+00:00
-- url     : https://prove2.me/theorems/e13d44df-2a07-47d1-aa2c-175cf51e760e
-- title:
--   Lemma E.1 — finite population and sample-moment promise
-- statement:
--   Let $T,M\ge1$, $U,V$ orthonormal frames, $\epsilon,H,\Delta,L_0,\sigma>0$, and let $C_N\ge0$ satisfy $\mathbb E\,\mathrm{Lip}(N_j)^2\le C_N\sigma^2$ for the composed noise field. Under (127),
--   $$12\lambda T\le\Delta,\qquad\frac{\lambda}{b}\bigl(c_*\sqrt T+C_*+\sqrt{C_N}\sigma\bigr)\le\frac{L_0}{2},\qquad c_*=37,\ C_*=9147,$$
--   the paired samples $f_{j,\pm}$ have population mean $\lambda F_{\mathrm{new}}(\cdot/b)$ for every realization, $\mathbb E S_M\le L_0^2/4$, and in particular $\mathbb P(E_{\mathrm{adm}})\ge3/4$ for $E_{\mathrm{adm}}=\{S_M\le L_0^2\}$. Moreover, on $E_{\mathrm{adm}}$ the population belongs to the class (2): its mean is $H$-smooth and has gap at most $\Delta$.
--
--   Differences from the source:
--   - generalization: random frames; a uniformly random hiding permutation → every fixed pair of orthonormal frames and every permutation; expectation over the tensors; reason: specializes to random frames and permutation by averaging
--   - generalization: conclusions: mean, E S_M, P(E_adm) → also: on E_adm the population is admissible (H-smooth mean, gap ≤ Δ, moment ≤ L₀²); reason: established in the proof (p.66: λF_new(·/b) is H-smooth) and used by Lemma E.5
--   - encoding: C_N with E Lip(N_j)² ≤ C_Nσ² → C_N ≥ 0 with that hypothesis for the composed field; reason: as stated on p.66
--   - encoding: physical space ℝᵈ, d = r + m → E (r+m) split by the isometry splitIso; reason: Lean convention
--   - encoding: M independent base functions → M ≥ 1; reason: the population is nonempty; at M = 0 the mean of the empty family is 0
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma E.1, p.66, (126)–(129)

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible
import Definitions.Def_ZOGlobalLB_Population

open MeasureTheory
open scoped ENNReal

namespace ZOGlobalLB

/-- **Lemma E.1 (Finite population and sample-moment promise).** Xia, Yuan, arXiv:2610.19652,
Lemma E.1, p.66, (126)–(129).

Let `1 ≤ T`, `M ≥ 1`, `U`, `V` orthonormal frames, `ϵ, H, σ > 0`, and let `C_N ≥ 0` satisfy
`E Lip(N_j)² ≤ C_N σ²` for the composed noise field. Under (127),
`12λT ≤ Δ` and `(λ/b)(c*√T + C* + √C_N σ) ≤ L₀/2` with `c* = 37`, `C* = 9147`, the paired
samples (128) have population mean `λF_new(·/b)` for every realization, and `E S_M ≤ L₀²/4`. In
particular, `P(E_adm) ≥ 3/4`, where `E_adm = {S_M ≤ L₀²}` (129).

The lemma's proof also establishes, and the statement records, that `λF_new(·/b)` is globally
`H`-smooth and has gap at most `Δ`, so that on `E_adm` the population belongs to the class (2).

**Formalization Note.**
* The frames are fixed and the expectation is over the Gaussian tensors (law `gaussArr`); since
  the statement holds for every pair of frames, it also holds for random frames. The hiding
  permutation `π` is arbitrary (the mean and `S_M` do not depend on it).
* The physical space is `ℝ^{r+m}`, split by `splitIso`; `·/b` is `X ↦ b⁻¹ • splitIso X`.
* The moment hypothesis is on one base label; all base labels have the same law. -/
theorem lemma_E_1 {r m T M : ℕ} (hT : 1 ≤ T) (hM : 1 ≤ M)
    (U : Fin T → E r) (V : Fin T → E m) (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)
    {ε H Δ L₀ σ C_N : ℝ} (hε : 0 < ε) (hH : 0 < H) (hΔ : 0 < Δ) (hL₀ : 0 < L₀) (hσ : 0 < σ)
    (hCN : 0 ≤ C_N)
    (hmom : ∫⁻ G, lipConst (noiseNZ σ U V G) ^ 2 ∂(gaussArr (Fin T × Idx m)) ≤
      ENNReal.ofReal (C_N * σ ^ 2))
    (h127a : 12 * lamScale ε H * T ≤ Δ)
    (h127b : lamScale ε H / bScale ε H * (cStar * Real.sqrt T + CStar + Real.sqrt C_N * σ) ≤
      L₀ / 2)
    (π : Equiv.Perm (Fin (M + M))) :
    (∀ (G : Fin M × (Fin T × Idx m) → ℝ) (X : E (r + m)),
      popMean (population ε H σ U V π G) X =
        lamScale ε H * Fnew U V ((bScale ε H)⁻¹ • splitIso r m X)) ∧
    ∫⁻ G, sampleMoment ε H σ U V π G ∂(gaussArr (Fin M × (Fin T × Idx m))) ≤
      ENNReal.ofReal (L₀ ^ 2 / 4) ∧
    (3 / 4 : ℝ≥0∞) ≤ gaussArr (Fin M × (Fin T × Idx m))
      {G | sampleMoment ε H σ U V π G ≤ ENNReal.ofReal (L₀ ^ 2)} ∧
    ∀ G : Fin M × (Fin T × Idx m) → ℝ, sampleMoment ε H σ U V π G ≤ ENNReal.ofReal (L₀ ^ 2) →
      Admissible Δ H L₀ (population ε H σ U V π G) := by sorry

end ZOGlobalLB
