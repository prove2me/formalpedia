-- Prove2me | Theorems.Thm_buchstab4dt_chaining
-- name    : buchstab4dt_chaining
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T11:30:33.829338+00:00
-- url     : https://prove2.me/theorems/2f8b2d9f-bc50-4e57-8676-e9458664abc6
-- title:
--   Certified interval monotonicity, antitone, peak-envelope, and transition bounds for 4D Buchstab integrals
-- statement:
--   For any valid parameter tuple $p \in \mathrm{Params4DT}$ and any Buchstab function $\omega$ satisfying `IsBuchstabCore`, this theorem certifies the five interval-chaining rules used to bound
--   $$I(\varphi) = \int_{\Omega_{A,B,C}} \frac{\omega\!\left(\frac{\varphi - \sum_{j=0}^3 x_j}{x_2}\right)}{x_0 x_1 x_2^2 x_3}\, dx$$
--   uniformly over $\varphi \in [2, 7/2]$.
--
--   Specifically, using only integer evaluations of `evalTree3` and `evalTree4`, it proves:
--   1. **Increasing-interval chaining**: if `evalTree3 (evalMmLeaf p pa pb)` has positive part $\le$ negative part, then $I(\varphi) \le I(p_b/D_p)$ on $[p_a/D_p, p_b/D_p]$.
--   2. **Decreasing-interval chaining**: if `evalTree3 (evalMpLeaf p pa pb)` has positive part $\le$ negative part, then $I(\varphi) \le I(p_a/D_p)$ on $[p_a/D_p, p_b/D_p]$.
--   3. **Left and right peak envelopes**: combining a 4D endpoint bound at $p_s/D_p$ with a 3D slope-difference bound yields $I(\varphi) \le \mathrm{bnd}_n / S_4$ across the peak neighborhood.
--   4. **Upper transition bound**: for $\varphi \ge p_a/D_p \ge 4B + C$, `evalTree4 (eval4TransLeaf p pa)` certifies $I(\varphi) \le \mathrm{bnd}_n / S_4$.
-- source:
--   Wu (2004), Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114 (2004), 215-273; reusable 4D Buchstab integral certification framework for LL_Decomp587j.r1j17_short and LL_Decomp587l.r0j17_short.

import Mathlib
import Definitions.Def_Buchstab4DT_Core

open Real Set MeasureTheory Buchstab4DT
open scoped Classical

theorem buchstab4dt_chaining :
∀ (p : Params4DT), p.Valid → ∀ {ω : ℝ → ℝ}, IsBuchstabCore ω →
  (∀ {pa_n pb_n : ℕ} {t : BoxTree3},
    pa_n ≤ pb_n → (pb_n : ℝ) / p.D_p ≤ 5 * p.A_R + p.B_R →
    tree3Valid .simp t = true →
    (let r := evalTree3 (evalMmLeaf p pa_n pb_n) .simp t p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n; r.1 ≤ r.2) →
    ∀ {φ : ℝ}, (pa_n : ℝ) / p.D_p ≤ φ → φ ≤ (pb_n : ℝ) / p.D_p →
    I_fn p ω φ ≤ I_fn p ω ((pb_n : ℝ) / p.D_p)) ∧
  (∀ {pa_n pb_n : ℕ} {t : BoxTree3},
    pa_n ≤ pb_n → (pb_n : ℝ) / p.D_p ≤ 5 * p.A_R + p.B_R →
    tree3Valid .simp t = true →
    (let r := evalTree3 (evalMpLeaf p pa_n pb_n) .simp t p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n; r.1 ≤ r.2) →
    ∀ {φ : ℝ}, (pa_n : ℝ) / p.D_p ≤ φ → φ ≤ (pb_n : ℝ) / p.D_p →
    I_fn p ω φ ≤ I_fn p ω ((pa_n : ℝ) / p.D_p)) ∧
  (∀ {bnd_n pa_n ps_n : ℕ} {t3 : BoxTree3} {t4 : BoxTree4},
    pa_n ≤ ps_n → (ps_n : ℝ) / p.D_p ≤ 5 * p.A_R + p.B_R →
    tree3Valid .simp t3 = true → tree4Valid .simp t4 = true →
    (let r := evalTree3 (evalMmLeaf p pa_n ps_n) .simp t3 p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n
     let v := evalTree4 (eval4Leaf p ps_n) .simp t4 p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n p.B_n p.C_n
     v * p.D_p + (r.1 - r.2) * (ps_n - pa_n) * 100 ≤ bnd_n * p.D_p) →
    ∀ {φ : ℝ}, (pa_n : ℝ) / p.D_p ≤ φ → φ ≤ (ps_n : ℝ) / p.D_p →
    I_fn p ω φ ≤ (bnd_n : ℝ) / p.S_4) ∧
  (∀ {bnd_n ps_n pb_n : ℕ} {t3 : BoxTree3} {t4 : BoxTree4},
    ps_n ≤ pb_n → (pb_n : ℝ) / p.D_p ≤ 5 * p.A_R + p.B_R →
    tree3Valid .simp t3 = true → tree4Valid .simp t4 = true →
    (let r := evalTree3 (evalMpLeaf p ps_n pb_n) .simp t3 p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n
     let v := evalTree4 (eval4Leaf p ps_n) .simp t4 p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n p.B_n p.C_n
     v * p.D_p + (r.1 - r.2) * (pb_n - ps_n) * 100 ≤ bnd_n * p.D_p) →
    ∀ {φ : ℝ}, (ps_n : ℝ) / p.D_p ≤ φ → φ ≤ (pb_n : ℝ) / p.D_p →
    I_fn p ω φ ≤ (bnd_n : ℝ) / p.S_4) ∧
  (∀ {bnd_n pa_n : ℕ} {t4 : BoxTree4},
    p.D_p * (4 * p.B_n + p.C_n) ≤ pa_n * p.D_x →
    tree4Valid .simp t4 = true →
    evalTree4 (eval4TransLeaf p pa_n) .simp t4 p.A_n p.B_n p.A_n p.B_n p.A_n p.B_n p.B_n p.C_n ≤ bnd_n →
    ∀ {φ : ℝ}, (pa_n : ℝ) / p.D_p ≤ φ →
    I_fn p ω φ ≤ (bnd_n : ℝ) / p.S_4) := by sorry
