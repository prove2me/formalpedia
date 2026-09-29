-- Prove2me | Theorems.Thm_exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq
-- name    : exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/3fbbad5b-e67c-5c78-8b84-c314e546aaad
-- title:
--   Inversion of Abel's half-line integral equation, smooth families
-- statement:
--   Let $P$ be a real normed space (a type with a normed additive commutative group structure and a real normed space structure). The assertion is the existence of an operator $T$ carrying functions $\mathbb{R} \to \mathbb{C}$ to functions $\mathbb{R} \to \mathbb{C}$ with the following two properties. First, $T$ is $\mathbb{C}$-linear on smooth compactly supported data: for all $f, g : \mathbb{R} \to \mathbb{C}$ that are $C^\infty$ with compact support and all $a, b \in \mathbb{C}$, one has $T(a f + b g) = a\, T f + b\, T g$ as functions of $\xi$. Second, for every $G : \mathbb{R} \times P \to \mathbb{C}$ that is $C^\infty$ with compact support, three things hold: the function $(\xi, p) \mapsto T(G(\cdot, p))(\xi)$ on $\mathbb{R} \times P$ is $C^\infty$; for every $R \in \mathbb{R}$, if $G(\xi, p) = 0$ for all $p \in P$ and all $\xi \ge R$, then also $T(G(\cdot, p))(\xi) = 0$ for all $p \in P$ and all $\xi \ge R$; and for every $\eta \in \mathbb{R}$ and every $p \in P$, the Bochner integral of $\xi \mapsto T(G(\cdot, p))(\xi) / \sqrt{\xi - \eta}$ over the open half-line $(\eta, \infty)$, with respect to Lebesgue measure, equals $G(\eta, p)$. No constraint is imposed on the values of $T$ at functions outside the smooth compactly supported ones.
--
--   This is the solvability of Abel's integral equation with kernel $(\xi - \eta)^{-1/2}$ on a half-line, in a form uniform in an auxiliary parameter $p$ in a normed space: the solution operator is linear, preserves smoothness jointly in $(\xi, p)$, and propagates vanishing on upper half-lines. It is used in the construction of the archimedean splitting transform for automorphic forms on $\mathrm{GL}_2(\mathbb{R})$, via [`AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq`](thm.html#AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq.lean

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Sqrt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ T : (ℝ → ℂ) → (ℝ → ℂ),
      (∀ f g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, T (fun ξ => a * f ξ + b * g ξ) = fun ξ => a * T f ξ + b * T g ξ) ∧
      ∀ G : ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => T (fun ξ => G (ξ, q.2)) q.1) ∧
        (∀ R : ℝ, (∀ (p : P) (ξ : ℝ), R ≤ ξ → G (ξ, p) = 0) →
          ∀ (p : P) (ξ : ℝ), R ≤ ξ → T (fun ξ' => G (ξ', p)) ξ = 0) ∧
        ∀ (η : ℝ) (p : P),
          ∫ ξ in Set.Ioi η, T (fun ξ' => G (ξ', p)) ξ / ((Real.sqrt (ξ - η) : ℝ) : ℂ) = G (η, p) := by sorry
