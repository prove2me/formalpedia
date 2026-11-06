-- Prove2me | Theorems.Thm_ZOGlobalLB_theorem_D_1
-- name    : ZOGlobalLB.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:50:26.80089+00:00
-- url     : https://prove2.me/theorems/a0f11eab-1744-4cf8-bace-ac46a853f978
-- title:
--   Theorem D.1 — uniform global sample-noise moment
-- statement:
--   There is a constant $C_A>0$ (depending only on the fixed $A=128$) such that for all $T\ge1$, $\sigma>0$ and orthonormal frames $U,V$, with the independent stage tensors defining (34),
--   $$\mathbb E\,\mathrm{Lip}_{(w,x)}(N_j)^2\le C_A\sigma^2\,\frac{m+T+\log(2T)}{m},$$
--   and the same bound holds for the composed field $(z,x)\mapsto N_j(U^\top y(z),x)$. When $m\ge T$ the right-hand side is at most a universal multiple of $\sigma^2$, independently of $T$. For $m\ge\max\{T,8\}$ the composed field satisfies
--   $$\mathbb E\,\mathrm{Lip}(N_j)^2\le C_N\sigma^2,\qquad C_N=2^{128}.$$
--
--   The noise added at all $T$ stages therefore costs only $O(\sigma^2)$ of the sample Lipschitz budget, not $O(T\sigma^2)$.
--
--   Differences from the source:
--   - encoding: C_A universal → ∃ C_A quantified before m, T, σ, U, V; reason: uniformity
--   - encoding: expectation over the stage tensors → ∫⁻ over gaussArr for every pair of orthonormal frames, plus a.e.-measurability of the Lipschitz constant; reason: the estimates are uniform over the frames (p.21); measurability makes ∫⁻ the expectation
--   - reading: the same order bound holds after composition → the same constant C_A for the composed field; reason: take the larger of the two constants
--   - reading: in particular, when m ≥ T → no separate clause; reason: (m+T+log 2T)/m ≤ 3 when T ≤ m
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem D.1, p.56; constants pp.64–65

import Mathlib
import Definitions.Def_ZOGlobalLB_lipConst
import Definitions.Def_ZOGlobalLB_NoiseField

open MeasureTheory
open scoped ENNReal

namespace ZOGlobalLB

/-- **Theorem D.1 (Uniform global sample-noise moment).** Xia, Yuan, arXiv:2610.19652,
Theorem D.1, p.56.

There is a constant `C_A > 0` (depending only on the fixed `A = 128`) such that, for the
independent stage tensors defining (34),
`E Lip_{(w,x)}(N_j)² ≤ C_A σ² (m + T + log(2T))/m`; in particular, when `m ≥ T`, the right-hand
side is at most a universal multiple of `σ²`, independently of `T`. The same order bound holds
after composition with the soft coordinate map `(z, x) ↦ N_j(Uᵀ y(z), x)`. For `m ≥ max{T, 8}`
the composed field admits `C_N = 2¹²⁸`: `E Lip(N_j)² ≤ C_N σ²`.

**Formalization Note.**
* `C_A` is quantified before `m, T, σ, U, V`: it is universal.
* The bounds hold for every pair of orthonormal frames (p.21: "The estimates are uniform over the
  hidden frames"); the expectation is over the tensors only, with law `gaussArr (Fin T × Idx m)`.
* `m ≥ T` and `r ≥ T` follow from orthonormality of `V` and `U`; the "in particular" sentence is a
  consequence of the first bound, since `(m + T + log 2T)/m ≤ 3` when `T ≤ m`.
* Lipschitz constants are `lipConst` (`ℝ≥0∞`); the expectations are `∫⁻`, and the integrands are
  also stated a.e.-measurable, so the lower integral is the expectation.
* One `C_A` serves the field and its composition (take the larger of two constants). -/
theorem theorem_D_1 :
    ∃ CA : ℝ, 0 < CA ∧
      ∀ {r m T : ℕ} (σ : ℝ), 0 < σ → 1 ≤ T →
        ∀ (U : Fin T → E r) (V : Fin T → E m), Orthonormal ℝ U → Orthonormal ℝ V →
          AEMeasurable (fun G => lipConst (noiseNP σ V G)) (gaussArr (Fin T × Idx m)) ∧
          ∫⁻ G, lipConst (noiseNP σ V G) ^ 2 ∂(gaussArr (Fin T × Idx m)) ≤
            ENNReal.ofReal (CA * σ ^ 2 * (m + T + Real.log (2 * T)) / m) ∧
          AEMeasurable (fun G => lipConst (noiseNZ σ U V G)) (gaussArr (Fin T × Idx m)) ∧
          ∫⁻ G, lipConst (noiseNZ σ U V G) ^ 2 ∂(gaussArr (Fin T × Idx m)) ≤
            ENNReal.ofReal (CA * σ ^ 2 * (m + T + Real.log (2 * T)) / m) ∧
          (8 ≤ m →
            ∫⁻ G, lipConst (noiseNZ σ U V G) ^ 2 ∂(gaussArr (Fin T × Idx m)) ≤
              ENNReal.ofReal (2 ^ 128 * σ ^ 2)) := by sorry

end ZOGlobalLB
