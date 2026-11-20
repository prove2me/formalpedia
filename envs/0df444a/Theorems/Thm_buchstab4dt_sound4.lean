-- Prove2me | Theorems.Thm_buchstab4dt_sound4
-- name    : buchstab4dt_sound4
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T11:30:28.311298+00:00
-- url     : https://prove2.me/theorems/2b75dc8c-9c98-4453-b581-245b33022f28
-- title:
--   Soundness of 4D Buchstab leaf/tree evaluators and 3D Fubini-difference reduction
-- statement:
--   For any valid grid parameter configuration $p \in \mathrm{Params4DT}$, this theorem establishes the soundness of the integer-arithmetic 4D Buchstab integral evaluators and the reduction to a 3D inner integral.
--
--   Specifically, for every valid parameter tuple $p$:
--   1. Exact scaling identities relating the integer evaluators `cut3Num` and `ramp3Num` to the continuous inclusion-exclusion sums `cut3SumR` and `ramp3SumR`.
--   2. Pointwise leaf soundness for `eval4Leaf` (in the regime $\varphi \le 5A + B$ where $\omega(u) = 1/u$ on $[1,2]$) and `eval4TransLeaf` (in the upper transition regime $\varphi \ge 4B + C$), together with tree-additivity for `evalTree4` over arbitrary valid `BoxTree4` partitions.
--   3. The Fubini representation
--   $$I(\varphi) = \int_{\Delta_{A,B}} \frac{1}{y_0 y_1 y_2}\, G(\varphi, y)\, dy$$
--   for $\varphi \le 5A + B$, the exact difference decomposition of $G(\varphi_2, y) - G(\varphi_1, y)$ into a boundary gain minus an interior drop, integrability of the 3D integrand, and tree-additivity for signed 3D difference bounds via `evalTree3`.
-- source:
--   Wu (2004), Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114 (2004), 215-273; reusable 4D Buchstab integral certification framework for LL_Decomp587j.r1j17_short and LL_Decomp587l.r0j17_short.

import Mathlib
import Definitions.Def_Buchstab4DT_Core

open Real Set MeasureTheory Buchstab4DT
open scoped Classical

theorem buchstab4dt_sound4 :
∀ (p : Params4DT), p.Valid →
  (∀ {dx0 dx1 dx2 r : ℕ},
    ((cut3Num p dx0 dx1 dx2 r : ℝ) / (12 * (p.D_p : ℝ) ^ 3 * (p.D_x : ℝ) ^ 3)) =
      cut3SumR ((dx0 : ℝ) / p.D_x) ((dx1 : ℝ) / p.D_x) (2 * ((dx2 : ℝ) / p.D_x)) ((r : ℝ) / ((p.D_p : ℝ) * p.D_x)) / 12) ∧
  (∀ {dx0 dx1 dx2 r : ℕ},
    ((ramp3Num p dx0 dx1 dx2 r : ℝ) / (48 * (p.D_p : ℝ) ^ 4 * (p.D_x : ℝ) ^ 4)) =
      ramp3SumR ((dx0 : ℝ) / p.D_x) ((dx1 : ℝ) / p.D_x) (2 * ((dx2 : ℝ) / p.D_x)) ((r : ℝ) / ((p.D_p : ℝ) * p.D_x)) / 48) ∧
  (∀ {knd n0a n0b n1a n1b n2a n2b}, cell3Valid p knd n0a n0b n1a n1b n2a n2b →
    cell3Ok knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x) ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x)) ∧
  (∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ {p_n : ℕ}, (p_n : ℝ) / p.D_p ≤ 5 * p.A_R + p.B_R →
    ∀ {knd n0a n0b n1a n1b n2a n2b n3a n3b}, cell4Valid p knd n0a n0b n1a n1b n2a n2b n3a n3b →
    ∫ x in cell4Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x)
                        ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x) ((n3a : ℝ) / p.D_x) ((n3b : ℝ) / p.D_x),
      ω (((p_n : ℝ) / p.D_p - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
      (eval4Leaf p p_n knd n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / p.S_4) ∧
  (∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ {pa_n : ℕ} {φ : ℝ}, (pa_n : ℝ) / p.D_p ≤ φ →
    p.D_p * (4 * p.B_n + p.C_n) ≤ pa_n * p.D_x →
    ∀ {knd n0a n0b n1a n1b n2a n2b n3a n3b}, cell4Valid p knd n0a n0b n1a n1b n2a n2b n3a n3b →
    ∫ x in cell4Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x)
                        ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x) ((n3a : ℝ) / p.D_x) ((n3b : ℝ) / p.D_x),
      ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
      (eval4TransLeaf p pa_n knd n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / p.S_4) ∧
  (∀ {ω : ℝ → ℝ}, IsBuchstabCore ω →
    ∀ (lfFn : CellKind → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) (φ : ℝ),
    (∀ knd n0a n0b n1a n1b n2a n2b n3a n3b, cell4Valid p knd n0a n0b n1a n1b n2a n2b n3a n3b →
      ∫ x in cell4Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x)
                          ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x) ((n3a : ℝ) / p.D_x) ((n3b : ℝ) / p.D_x),
        ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
        (lfFn knd n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / p.S_4) →
    ∀ (t : BoxTree4) (knd : CellKind) (n0a n0b n1a n1b n2a n2b n3a n3b : ℕ),
      tree4Valid knd t = true → cell4Valid p knd n0a n0b n1a n1b n2a n2b n3a n3b →
      ∫ x in cell4Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x)
                          ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x) ((n3a : ℝ) / p.D_x) ((n3b : ℝ) / p.D_x),
        ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤
        (evalTree4 lfFn knd t n0a n0b n1a n1b n2a n2b n3a n3b : ℝ) / p.S_4) ∧
  (∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ {φ : ℝ}, φ ≤ 5 * p.A_R + p.B_R →
    I_fn p ω φ = ∫ y in cell3Set .simp p.A_R p.B_R p.A_R p.B_R p.A_R p.B_R,
      (1 / (y 0 * y 1 * y 2)) * G_fn p φ y) ∧
  (∀ {φ1 φ2 : ℝ}, φ1 < φ2 → ∀ {y : Fin 3 → ℝ}, 0 < y 2 →
    let m1 := max p.B_R (min p.C_R (φ1 - y 0 - y 1 - 2 * y 2))
    let m2 := max p.B_R (min p.C_R (φ2 - y 0 - y 1 - 2 * y 2))
    G_fn p φ2 y - G_fn p φ1 y =
      (∫ x3 in m1..m2, 1 / (x3 * (φ2 - (y 0 + y 1 + y 2) - x3))) -
      (φ2 - φ1) * (∫ x3 in p.B_R..m1, 1 / (x3 * (φ1 - (y 0 + y 1 + y 2) - x3) * (φ2 - (y 0 + y 1 + y 2) - x3)))) ∧
  (∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ {φ : ℝ}, φ ≤ 5 * p.A_R + p.B_R →
    ∀ {knd n0a n0b n1a n1b n2a n2b}, cell3Valid p knd n0a n0b n1a n1b n2a n2b →
    IntegrableOn (fun y : Fin 3 → ℝ => (1 / (y 0 * y 1 * y 2)) * G_fn p φ y)
      (cell3Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x) ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x)) volume) ∧
  (∀ {F : (Fin 3 → ℝ) → ℝ},
    (∀ knd n0a n0b n1a n1b n2a n2b, cell3Valid p knd n0a n0b n1a n1b n2a n2b →
      IntegrableOn F (cell3Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x) ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x)) volume) →
    ∀ (lfFn : CellKind → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat),
    (∀ knd n0a n0b n1a n1b n2a n2b, cell3Valid p knd n0a n0b n1a n1b n2a n2b →
      let r := lfFn knd n0a n0b n1a n1b n2a n2b
      ∫ y in cell3Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x) ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x), F y ≤
        ((r.1 : ℝ) - (r.2 : ℝ)) / p.S_3) →
    ∀ (t : BoxTree3) (knd : CellKind) (n0a n0b n1a n1b n2a n2b : ℕ),
      tree3Valid knd t = true → cell3Valid p knd n0a n0b n1a n1b n2a n2b →
      let r := evalTree3 lfFn knd t n0a n0b n1a n1b n2a n2b
      ∫ y in cell3Set knd ((n0a : ℝ) / p.D_x) ((n0b : ℝ) / p.D_x) ((n1a : ℝ) / p.D_x) ((n1b : ℝ) / p.D_x) ((n2a : ℝ) / p.D_x) ((n2b : ℝ) / p.D_x), F y ≤
        ((r.1 : ℝ) - (r.2 : ℝ)) / p.S_3) := by sorry
