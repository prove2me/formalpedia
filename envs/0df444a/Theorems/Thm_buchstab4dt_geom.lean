-- Prove2me | Theorems.Thm_buchstab4dt_geom
-- name    : buchstab4dt_geom
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T11:30:40.222181+00:00
-- url     : https://prove2.me/theorems/7ef8b4be-2bc1-4a4a-b9b7-0b3ec1b524de
-- title:
--   Buchstab bounds, Hermite-Hadamard/Jensen cell inequalities, and exact cut/ramp integrals in 3D and 4D
-- statement:
--   This theorem packages the parameter-independent analytic and geometric primitives used to certify four-dimensional Buchstab integrals over triangular-simplex cells.
--
--   Specifically, it establishes:
--   1. Pointwise bounds for any Buchstab function $\omega$ satisfying `IsBuchstabCore`: $0 \le \omega(u) \le 1$ for all $u \in \mathbb{R}$, and $\omega(u) \le \max(1/u, 2/3)$ for $u \ge 1$.
--   2. Convexity of reciprocals of products of positive affine functionals, together with the 1D, 3D, and 4D Hermite--Hadamard upper bounds and 1D/3D Jensen lower bounds on the cell families `box`, `tri01`, `tri12`, and `simp`.
--   3. Measure-preserving Fubini splitting between $\mathbb{R}^4$ and $\mathbb{R} \times \mathbb{R}^3$, compactness and convexity of all 3D/4D cells, and iterated-integral formulas for continuous integrands.
--   4. Exact inclusion-exclusion formulas for the 3D cut volume, 3D linear ramp integral, and 4D cut volume on boxes, together with the symmetry inequality comparing a triangular cell to $1/\mathrm{facDen}$ times its enclosing box for nonnegative antitone functions of $x_0 + x_1 + 2x_2$.
--
--   These primitives are completely independent of the grid parameters and can be reused across any 4D Buchstab integral bound.
-- source:
--   Wu (2004), Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114 (2004), 215-273; reusable 4D Buchstab integral certification framework for LL_Decomp587j.r1j17_short and LL_Decomp587l.r0j17_short.

import Mathlib
import Definitions.Def_Buchstab4DT_Core

open Real Set MeasureTheory Buchstab4DT
open scoped Classical

theorem buchstab4dt_geom :
(∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ u, 0 ≤ ω u) ∧
(∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ {u : ℝ}, 1 ≤ u → ω u ≤ max (1 / u) (2 / 3)) ∧
(∀ {ω : ℝ → ℝ}, IsBuchstabCore ω → ∀ u, ω u ≤ 1) ∧
(∀ {E : Type} [AddCommGroup E] [Module ℝ E] {S : Set E}, Convex ℝ S →
  ∀ {k : ℕ} (L : Fin k → E → ℝ),
    (∀ i, ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      L i (a • x + b • y) = a * L i x + b * L i y) →
    (∀ i, ∀ x ∈ S, 0 < L i x) →
    ConvexOn ℝ S (fun x => (∏ i : Fin k, L i x)⁻¹)) ∧
(∀ {a b : ℝ}, a ≤ b → ∀ {f : ℝ → ℝ}, ConvexOn ℝ (Icc a b) f → ContinuousOn f (Icc a b) →
  ∫ x in a..b, f x ≤ ((b - a) / 2) * (f a + f b)) ∧
(∀ {a b : ℝ}, a ≤ b → ∀ {f : ℝ → ℝ}, ConvexOn ℝ (Icc a b) f → ContinuousOn f (Icc a b) →
  (b - a) * f ((a + b) / 2) ≤ ∫ x in a..b, f x) ∧
(MeasurePreserving equivFin4_3 (volume : Measure (Fin 4 → ℝ))
  ((volume : Measure ℝ).prod (volume : Measure (Fin 3 → ℝ)))) ∧
(∀ x : Fin 4 → ℝ, equivFin4_3 x = (x 3, ![x 0, x 1, x 2])) ∧
(∀ knd a0 b0 a1 b1 a2 b2 a3 b3,
  cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3 =
    equivFin4_3 ⁻¹' (Icc a3 b3 ×ˢ cell3Set knd a0 b0 a1 b1 a2 b2)) ∧
(∀ knd a0 b0 a1 b1 a2 b2, IsClosed (cell3Set knd a0 b0 a1 b1 a2 b2)) ∧
(∀ knd a0 b0 a1 b1 a2 b2, IsCompact (cell3Set knd a0 b0 a1 b1 a2 b2)) ∧
(∀ knd a0 b0 a1 b1 a2 b2 a3 b3, IsClosed (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3)) ∧
(∀ knd a0 b0 a1 b1 a2 b2 a3 b3, IsCompact (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3)) ∧
(∀ knd a0 b0 a1 b1 a2 b2, Convex ℝ (cell3Set knd a0 b0 a1 b1 a2 b2)) ∧
(∀ knd a0 b0 a1 b1 a2 b2 a3 b3, Convex ℝ (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3)) ∧
(∀ (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}, a0 ≤ b0 → a1 ≤ b1 → a2 ≤ b2 →
  ∀ {f : (Fin 3 → ℝ) → ℝ}, ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2) →
  ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, f x =
    match knd with
    | .box => ∫ x0 in a0..b0, ∫ x1 in a1..b1, ∫ x2 in a2..b2, f ![x0, x1, x2]
    | .tri01 => ∫ x2 in a2..b2, ∫ x1 in a0..b0, ∫ x0 in a0..x1, f ![x0, x1, x2]
    | .tri12 => ∫ x0 in a0..b0, ∫ x2 in a1..b1, ∫ x1 in a1..x2, f ![x0, x1, x2]
    | .simp => ∫ x2 in a0..b0, ∫ x1 in a0..x2, ∫ x0 in a0..x1, f ![x0, x1, x2]) ∧
(∀ (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}, cell3Ok knd a0 b0 a1 b1 a2 b2 →
  ∀ {f : (Fin 3 → ℝ) → ℝ}, ConvexOn ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) f →
  ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2) →
  ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, f x ≤
    ((b0 - a0) * (b1 - a1) * (b2 - a2) / ((facDen knd : ℝ) * (nVerts3 knd : ℝ))) *
      sumVerts3R f knd a0 b0 a1 b1 a2 b2) ∧
(∀ (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ}, cell3Ok knd a0 b0 a1 b1 a2 b2 →
  ∀ {f : (Fin 3 → ℝ) → ℝ}, ConvexOn ℝ (cell3Set knd a0 b0 a1 b1 a2 b2) f →
  ContinuousOn f (cell3Set knd a0 b0 a1 b1 a2 b2) →
  ((b0 - a0) * (b1 - a1) * (b2 - a2) / (facDen knd : ℝ)) *
      f (centroid3R knd a0 b0 a1 b1 a2 b2) ≤
    ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, f x) ∧
(∀ (knd : CellKind) {a0 b0 a1 b1 a2 b2 a3 b3 : ℝ},
  cell3Ok knd a0 b0 a1 b1 a2 b2 → a3 ≤ b3 →
  ∀ {f : (Fin 4 → ℝ) → ℝ}, ConvexOn ℝ (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) f →
  ContinuousOn f (cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3) →
  ∫ x in cell4Set knd a0 b0 a1 b1 a2 b2 a3 b3, f x ≤
    ((b0 - a0) * (b1 - a1) * (b2 - a2) * (b3 - a3) / ((facDen knd : ℝ) * (2 * (nVerts3 knd : ℝ)))) *
      sumVerts3R (fun y => f ![y 0, y 1, y 2, a3] + f ![y 0, y 1, y 2, b3]) knd a0 b0 a1 b1 a2 b2) ∧
(∀ {c h R : ℝ}, 0 < c → 0 ≤ h →
  ∫ t in Icc (0 : ℝ) h, ({t : ℝ | c * t ≤ R}).indicator (fun _ => (1 : ℝ)) t =
    (max 0 R - max 0 (R - c * h)) / c) ∧
(∀ {a0 b0 a1 b1 a2 b2 L : ℝ}, a0 ≤ b0 → a1 ≤ b1 → a2 ≤ b2 →
  ∫ x in cell3Set .box a0 b0 a1 b1 a2 b2,
    ({x : Fin 3 → ℝ | x 0 + x 1 + 2 * x 2 ≤ L}).indicator (fun _ => (1 : ℝ)) x =
    cut3SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) (L - (a0 + a1 + 2 * a2)) / 12) ∧
(∀ {a0 b0 a1 b1 a2 b2 L : ℝ}, a0 ≤ b0 → a1 ≤ b1 → a2 ≤ b2 →
  ∫ x in cell3Set .box a0 b0 a1 b1 a2 b2, max 0 (L - (x 0 + x 1 + 2 * x 2)) =
    ramp3SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) (L - (a0 + a1 + 2 * a2)) / 48) ∧
(∀ {a0 b0 a1 b1 a2 b2 a3 b3 L : ℝ}, a0 ≤ b0 → a1 ≤ b1 → a2 ≤ b2 → a3 ≤ b3 →
  ∫ x in cell4Set .box a0 b0 a1 b1 a2 b2 a3 b3,
    ({x : Fin 4 → ℝ | x 0 + x 1 + 2 * x 2 + x 3 ≤ L}).indicator (fun _ => (1 : ℝ)) x =
    cut4SumR (b0 - a0) (b1 - a1) (2 * (b2 - a2)) (b3 - a3) (L - (a0 + a1 + 2 * a2 + a3)) / 48) ∧
(∀ (i : Fin 3) (m : ℝ), volume ({x : Fin 3 → ℝ | x i = m}) = 0) ∧
(∀ (knd : CellKind) {a0 b0 a1 b1 a2 b2 : ℝ},
  cell3Ok knd a0 b0 a1 b1 a2 b2 →
  ∀ {g : ℝ → ℝ}, (∀ s, 0 ≤ g s) → Antitone g →
  IntegrableOn (fun x : Fin 3 → ℝ => g (x 0 + x 1 + 2 * x 2)) (cell3Set .box a0 b0 a1 b1 a2 b2) volume →
  ∫ x in cell3Set knd a0 b0 a1 b1 a2 b2, g (x 0 + x 1 + 2 * x 2) ≤
    (1 / (facDen knd : ℝ)) * ∫ x in cell3Set .box a0 b0 a1 b1 a2 b2, g (x 0 + x 1 + 2 * x 2)) := by sorry
