-- Prove2me | Theorems.Thm_ZipkinLostSales_Variability_kappa_jointly_convex
-- name    : ZipkinLostSales.Variability.kappa_jointly_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:48.795721+00:00
-- url     : https://prove2.me/theorems/c792d2fb-f877-4acd-9068-0043931d10a6
-- title:
--   Proof of Theorem 11, p. 941 ("the key step") — κ̄_t(v, ζ | d) is jointly convex in (v, ζ, d)
-- statement:
--   Fix a lead time $L\ge1$, costs $\hat h,p\ge0$ and a discount factor $0<\gamma\le1$. Let $V=\{v\in\mathbb R^L:v_0\ge v_1\ge\dots\ge v_{L-1}\ge0\}$, with the convention $v_L=0$, and let $F:V\to\mathbb R$ (standing for the continuation cost $\bar f_{t+1}$) be convex and nonnegative on $V$. For $v\in V$, $\zeta\le0$ and $d\ge0$ let
--   $$\bar\kappa(v,\zeta\mid d)=\inf_{v_+}\Big\{\hat h(v_+-v_1)+p(v_+-v_0+d)+\gamma F\big[(v_+,v_2,\dots,v_{L-1},0)-\zeta e\big]:\ -d\le v_+-v_0\le0,\ v_+-v_1\ge0\Big\},$$
--   which is program (4). Then $\bar\kappa$ is jointly convex in $(v,\zeta,d)$ on the convex set
--   $$\{(v,\zeta,d):\ v\in V,\ \zeta\le0,\ d\ge0\}.$$
--
--   The paper calls this "the key step" of the proof of Theorem 11: since $\bar\kappa_t$ is convex in the demand $d$, its expectation increases when demand becomes larger in the convex order.
--
--   **Formalization Note** The continuation $F$ is generic; the result is applied with $F=\bar f_{t+1}$, which is convex on $V$ (Theorem 4) and nonnegative. Nonnegativity of $F$ keeps the infimum in (4) a genuine infimum rather than Lean's junk value. The domain is $d\ge0$: for $d<0$ the constraint set of (4) is empty. The infimum is over $v_+\in[\max(v_0-d,v_1),v_0]$, which is the constraint set of (4).
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 941 (PDF p. 6), proof of Theorem 11: "Moreover (this is the key step), κ̄_t is jointly convex in (v, ζ, d)."; program (4), p. 939 (PDF p. 4)

import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
open MeasureTheory

namespace ZipkinLostSales.Variability

/-- Proof of Theorem 11 (Zipkin 2008, p. 941, "the key step"): if the continuation `F` (standing
for `f̄_{t+1}`) is convex and nonnegative on `V`, then `κ̄(v, ζ | d)` of program (4) is jointly
convex in `(v, ζ, d)` on `{v ∈ ZipkinLostSales.LNatural.V, ζ ≤ 0, d ≥ 0}`. -/
theorem kappa_jointly_convex {L : ℕ} (hL : 0 < L) (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (F : (Fin L → ℝ) → ℝ) (hFconv : ConvexOn ℝ (ZipkinLostSales.LNatural.V L) F)
    (hFnonneg : ∀ v ∈ ZipkinLostSales.LNatural.V L, 0 ≤ F v) :
    ConvexOn ℝ {w : (Fin L → ℝ) × ℝ × ℝ | w.1 ∈ ZipkinLostSales.LNatural.V L ∧ w.2.1 ≤ 0 ∧ 0 ≤ w.2.2}
      (fun w => ZipkinLostSales.LNatural.kappa hh p γ F w.2.2 w.1 w.2.1) := by sorry

end ZipkinLostSales.Variability
