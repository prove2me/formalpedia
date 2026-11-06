-- Prove2me | Theorems.Thm_ZOGlobalLB_theorem_3_3
-- name    : ZOGlobalLB.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:50:15.715224+00:00
-- url     : https://prove2.me/theorems/94042546-ae00-43af-a9e0-aa4e4e381a4c
-- title:
--   Theorem 3.3 — reusable scalar information bound
-- statement:
--   Let $v$ be uniform on the unit sphere of a known $s$-dimensional subspace of $\mathbb R^m$, $s\ge4$, with the seed (initial auxiliary information and coins), $v$ and the fields independent. After $n$ adaptive evaluations of $\mu_v+Q_j$, with arbitrary label openings and reuse, every list of $M_{\mathrm{list}}$ transcript-measurable unit guesses $\hat v_1,\dots,\hat v_{M_{\mathrm{list}}}$ with $\log M_{\mathrm{list}}\le s/8$ satisfies
--   $$\mathbb P\Bigl(\max_{a\le M_{\mathrm{list}}}\langle v,\hat v_a\rangle\ge\frac{15}{16}\Bigr)\le\frac{64mn}{s^2\sigma^2}+\frac{9}{4s}.$$
--
--   For $s\asymp m$, constant-angle recovery of $v$ therefore needs $\Omega(m\sigma^2)$ evaluations, even when labels are reused.
--
--   Differences from the source:
--   - reading: log M_list ≤ s/8, printed beside the bound in (33) → a hypothesis; reason: the proof (p.55) uses it to bound the product-law hit probability; without it the bound fails for a list covering the sphere
--   - encoding: a known s-dimensional subspace → the image of an isometric embedding ι : ℝˢ → ℝᵐ; reason: same object
--   - encoding: transcript → the record: seed and the n replies; reason: the queries are functions of them
--   - reading: in particular, for s ≍ m, recovery costs Ω(mσ²) evaluations → no separate clause; reason: a consequence of the bound
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem 3.3, p.18, (33); proof p.55, (110)

import Mathlib
import Definitions.Def_ZOGlobalLB_OneStage
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere_v2

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace ZOGlobalLB

/-- **Theorem 3.3 (Reusable scalar information bound).** Xia, Yuan, arXiv:2610.19652,
Theorem 3.3, p.18, (33); proof p.55, (110).

Let `v` be uniform on the unit sphere of a known `s`-dimensional subspace of `ℝᵐ`, `s ≥ 4`. After
`n` adaptive evaluations of `μ_v + Q_j`, with arbitrary label openings and reuse, any list of
`M_list` transcript-measurable unit guesses `v̂_1, …, v̂_{M_list}` with `log M_list ≤ s/8`
satisfies `P(max_{a ≤ M_list} ⟨v, v̂_a⟩ ≥ 15/16) ≤ 64mn/(s²σ²) + 9/(4s)`. Initial auxiliary
information must be independent of `v` and its fields.

**Formalization Note.**
* `v = ι V` with `ι : ℝˢ → ℝᵐ` an isometric embedding (the known subspace) and `V` uniform on the
  unit sphere of `ℝˢ`. The seed `X₀` (coins and auxiliary information), `V` and the tensors `G`
  (law `gaussArr`) are mutually independent.
* The transcript is the record (seed and the `n` replies; the queries are functions of these);
  the guesses are measurable functions of it with unit norm.
* `log M_list ≤ s/8` is a hypothesis (`reading`): it is printed beside the bound in (33), and the
  proof (p.55) uses it to bound the product-law hit probability; without it the bound fails for
  a list that covers the sphere.
* "In particular, for `s ≍ m`, recovery costs `Ω(mσ²)` evaluations" is a remark that follows from
  the bound and is not a separate clause. -/
theorem theorem_3_3 {m s n Mlist : ℕ} (hs : 4 ≤ s) {σ : ℝ} (hσ : 0 < σ) {J S₀ : Type*}
    [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] [MeasurableSpace S₀]
    (ι : E s →ₗᵢ[ℝ] E m) (A : OneStageRule m J S₀)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → E s) (X₀ : Ω → S₀) (G : Ω → J × Idx m → ℝ)
    (hV : OnlineConvexOpt.BanditConvex.IsUniformOnUnitSphere P V) (hX₀ : Measurable X₀)
    (hG : HasLaw G (gaussArr (J × Idx m)) P)
    (hind : IndepFun (fun ω => (X₀ ω, V ω)) G P ∧ IndepFun X₀ V P)
    (guess : Fin Mlist → S₀ × (Fin n → ℝ) → E m) (hguess : ∀ a, Measurable (guess a))
    (hunit : ∀ a t, ‖guess a t‖ = 1) (hlist : Real.log Mlist ≤ (s : ℝ) / 8) :
    P {ω | ∃ a, (15 / 16 : ℝ) ≤
        ⟪ι (V ω), guess a (A.record σ (ι (V ω)) (X₀ ω) (G ω) n)⟫} ≤
      ENNReal.ofReal (64 * m * n / ((s : ℝ) ^ 2 * σ ^ 2) + 9 / (4 * s)) := by sorry

end ZOGlobalLB
