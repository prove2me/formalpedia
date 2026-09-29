-- Prove2me | Definitions.Def_Novelty_AiryODE
-- name    : Novelty_AiryODE
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:01:28.690992+00:00
-- url     : https://prove2.me/theorems/60f15e5a-48bd-4121-8f11-a9c30d24e959
-- title:
--   Aether Catalog definitions — Novelty_AiryODE
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AiryODE`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AiryODE.lean by skeleton subtraction
import Mathlib
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

namespace RandomMatrices

/-- The (classical, analytic) Wronskian of two functions `f, g` with first
derivatives `f'`, `g'`:  `W(x) = f(x)·g'(x) - f'(x)·g(x)`. -/
noncomputable def airyWronskian (f f' g g' : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x * g' x - f' x * g x




end RandomMatrices

/-
-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer):
  H1. For two solutions of the Airy equation `y'' = x y` (no first-order term),
      the Wronskian `W = f g' - f' g` is constant. [Abel's identity, edge-kernel
      backbone.]
  H2 (counter-intuitive). Constancy needs NO decay/integrability of the Airy
      function — it is purely local (a derivative computation) — even though the
      Airy *kernel* it powers is global (a Fredholm determinant).
  H3. Wronskian nonzero at one point ⇒ global linear independence of solutions.

Experiment (Experimenter):
  * H1: proved via the product rule and the ODE substitution; the cross terms
    `f' g'` cancel and `f g'' - f'' g = f(xg) - (xf)g = 0`. `is_const_of_deriv_eq_zero`
    upgrades pointwise `deriv = 0` to global constancy.
  * H3: differentiate the identity `a f + b g ≡ 0` once (derivative uniqueness),
    then solve the 2×2 system; `a W = 0` and `b W = 0`, and `W ≠ 0` forces `a=b=0`.

Analysis (Analyst):
  * H1, H3 SURVIVED (0 sorries). H2 confirmed: the proof uses only `HasDerivAt`
    data, never any growth/decay of `f` — the local nature is real, not an artifact.
  * Failure mode avoided: a naive `simp`/`ring` attempt on the Wronskian derivative
    fails because the ODE substitution must happen *before* the cancellation; the
    `rw [eqf, eqg]; ring` ordering is load-bearing.

Critique (Critic):
  * Not trivial: the proof uses the product rule, derivative uniqueness, and
    `is_const_of_deriv_eq_zero` (an MVT consequence). Not `rfl`/`decide`.
  * Hidden assumption checked: linear independence really needs `W ≠ 0` somewhere;
    if `W ≡ 0` the solutions are dependent — the hypothesis is exactly load-bearing.

Synthesis (PI):
  These two facts are reused in `AiryKernel.lean`: constancy of `W` is what makes
  the diagonal of the Christoffel–Darboux Airy kernel independent of position.
-/


