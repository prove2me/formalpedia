-- Prove2me | Theorems.Thm_RandomMatrices_airy_solutions_linearIndep
-- name    : RandomMatrices.airy_solutions_linearIndep
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:27:24.273312+00:00
-- url     : https://prove2.me/theorems/283b41a6-3ef6-4a2e-9757-540011daf6b4
-- title:
--   Linear independence of solutions.
-- statement:
--   **Linear independence of solutions.**  If the Wronskian of two solutions is
--   nonzero at some point `x₀`, then no nontrivial linear combination
--   `a·f + b·g` vanishes identically; hence `f` and `g` are linearly independent.
--
--   Note: only the first-derivative data is needed here (we differentiate the
--   identity `a·f + b·g ≡ 0` once and evaluate the `2×2` linear system at `x₀`).
--
--   ```lean
--   theorem RandomMatrices.airy_solutions_linearIndep    (f f' g g' : ℝ → ℝ)
--       (hf : ∀ x, HasDerivAt f (f' x) x)
--       (hg : ∀ x, HasDerivAt g (g' x) x)
--       (a b x0 : ℝ)
--       (hW : airyWronskian f f' g g' x0 ≠ 0)
--       (hcomb : ∀ x, a * f x + b * g x = 0) :
--       a = 0 ∧ b = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AiryODE.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AiryODE.lean#L76

-- Thm stub generated from Novelty/AiryODE.lean
import Mathlib
import Definitions.Def_Novelty_AiryODE
/-
# The Airy ODE: Wronskian Theory for Edge Universality

At the spectral *edge* of a random matrix ensemble the local eigenvalue statistics
are governed by the **Airy kernel**, built from solutions of Airy's differential
equation `y'' = x · y`.  The structural backbone of that kernel — the reason it is
an *integrable* (Christoffel–Darboux) kernel at all — is that the **Wronskian** of
two solutions of a second-order linear ODE with no first-order term is *constant*.

This file develops that analytic Wronskian theory directly for abstract solutions
`f, g : ℝ → ℝ` of the Airy equation (given via their first and second pointwise
derivatives), and proves:

* `airyWronskian_hasDerivAt_zero` — the Wronskian has derivative `0` everywhere
  (the one genuine computation: `W' = f·g'' - f''·g = f·(x·g) - (x·f)·g = 0`).
* `airyWronskian_const` — the Wronskian is constant.
* `airy_solutions_linearIndep` — two solutions whose Wronskian is nonzero at one
  point are linearly independent as functions.

These are the analytic inputs reused in `AiryKernel.lean` to compute the diagonal
of the Airy correlation kernel.
-/

open RandomMatrices

theorem RandomMatrices.airy_solutions_linearIndep    (f f' g g' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (a b x0 : ℝ)
    (hW : airyWronskian f f' g g' x0 ≠ 0)
    (hcomb : ∀ x, a * f x + b * g x = 0) :
    a = 0 ∧ b = 0 := by sorry
