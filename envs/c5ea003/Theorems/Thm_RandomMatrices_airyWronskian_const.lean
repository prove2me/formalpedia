-- Prove2me | Theorems.Thm_RandomMatrices_airyWronskian_const
-- name    : RandomMatrices.airyWronskian_const
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:27:19.481982+00:00
-- url     : https://prove2.me/theorems/f8eff623-306c-483a-b7e0-821d03a460c1
-- title:
--   Wronskian is constant.
-- statement:
--   **Wronskian is constant.**  Abel's identity for the Airy equation: the
--   Wronskian of two solutions takes the same value at every pair of points.
--
--   ```lean
--   theorem RandomMatrices.airyWronskian_const    (f f' f'' g g' g'' : ℝ → ℝ)
--       (hf : ∀ x, HasDerivAt f (f' x) x)
--       (hf' : ∀ x, HasDerivAt f' (f'' x) x)
--       (hg : ∀ x, HasDerivAt g (g' x) x)
--       (hg' : ∀ x, HasDerivAt g' (g'' x) x)
--       (eqf : ∀ x, f'' x = x * f x)
--       (eqg : ∀ x, g'' x = x * g x)
--       (a b : ℝ) :
--       airyWronskian f f' g g' a = airyWronskian f f' g g' b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AiryODE.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AiryODE.lean#L57

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

theorem RandomMatrices.airyWronskian_const    (f f' f'' g g' g'' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (eqf : ∀ x, f'' x = x * f x)
    (eqg : ∀ x, g'' x = x * g x)
    (a b : ℝ) :
    airyWronskian f f' g g' a = airyWronskian f f' g g' b := by sorry
