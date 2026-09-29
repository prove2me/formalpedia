-- Prove2me | Theorems.Thm_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd
-- name    : exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/4acbc58c-d937-57de-917d-80b7711b2492
-- title:
--   A linear Whitney–Hadamard operator, with smooth dependence on parameters
-- statement:
--   Let $P$ be a real normed space (a normed additive commutative group with a real normed space structure). The assertion is the existence of a single operator $W$ on complex-valued functions of one real variable, $W : (\mathbb{R} \to \mathbb{C}) \to (\mathbb{R} \to \mathbb{C})$, with three properties. First, $W$ is linear on smooth compactly supported functions: for all $f, g : \mathbb{R} \to \mathbb{C}$ that are $C^\infty$ with compact support and all $a, b \in \mathbb{C}$, one has $W(x \mapsto a f(x) + b g(x)) = (x \mapsto a\,(Wf)(x) + b\,(Wg)(x))$ as functions. Secondly, for every $C^\infty$ compactly supported $f$, the function $Wf$ is again $C^\infty$ with compact support, and: if $f$ is even, i.e. $f(-x) = f(x)$ for all real $x$, then $(Wf)(x^2) = f(x)$ for all real $x$; if $f$ is odd, i.e. $f(-x) = -f(x)$ for all real $x$, then $x \cdot (Wf)(x^2) = f(x)$ for all real $x$, the factor $x$ being its image in $\mathbb{C}$. Thirdly, $W$ acts well on families: for every $C^\infty$ compactly supported $H : \mathbb{R} \times P \to \mathbb{C}$, the function $(y, p) \mapsto \bigl(W(x \mapsto H(x, p))\bigr)(y)$ on $\mathbb{R} \times P$ is $C^\infty$ with compact support.
--
--   This packages Whitney's theorem on even smooth functions and the odd-function (Hadamard) variant into one operator that is simultaneously linear on test functions and compatible with smooth compactly supported families over a parameter space $P$. It is used in the analysis of archimedean weight characters for $\mathrm{GL}_2(\mathbb{R})$, in [`AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_one_splitTransform_eq`](thm.html#AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_one_splitTransform_eq) and [`AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq`](thm.html#AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq), where even and odd slices of a test function must be rewritten as functions of $x^2$ with control of smoothness and supports in the remaining variables.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd.lean

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ W : (ℝ → ℂ) → (ℝ → ℂ),
      (∀ f g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, W (fun x => a * f x + b * g x) = fun x => a * W f x + b * W g x) ∧
      (∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ContDiff ℝ (⊤ : ℕ∞) (W f) ∧ HasCompactSupport (W f) ∧
        ((∀ x : ℝ, f (-x) = f x) → ∀ x : ℝ, W f (x ^ 2) = f x) ∧
        ((∀ x : ℝ, f (-x) = -f x) → ∀ x : ℝ, (x : ℂ) * W f (x ^ 2) = f x)) ∧
      ∀ H : ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => W (fun x => H (x, q.2)) q.1) ∧
          HasCompactSupport (fun q : ℝ × P => W (fun x => H (x, q.2)) q.1) := by sorry
