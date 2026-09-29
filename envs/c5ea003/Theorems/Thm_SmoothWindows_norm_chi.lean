-- Prove2me | Theorems.Thm_SmoothWindows_norm_chi
-- name    : SmoothWindows.norm_chi
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:05:51.187712+00:00
-- url     : https://prove2.me/theorems/725b1c0c-d364-4161-a01a-9be57b5fb97f
-- title:
--   Norm chi
-- statement:
--   Formal statement of `SmoothWindows.norm_chi` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SmoothWindows.norm_chi(x : ℝ) : ‖chi x‖ = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/SmoothWindows/GaborOperators.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/SmoothWindows/GaborOperators.lean#L68

-- Thm stub generated from Algebra/SmoothWindows/GaborOperators.lean
import Mathlib
import Definitions.Def_Algebra_SmoothWindows_GaborOperators

/-!
# Smooth windows I: translation, modulation and the Weyl relation

The Reciprocal-Zero Harmonics programme (`Algebra.ReciprocalZeroHarmonics.Core`,
`Algebra.ReciprocalZeroHarmonics.WindowDichotomy`) analyses spectral data through the
*rectangular* window `|Im ρ| ≤ T`.  This file lays the algebraic foundation for replacing that
sharp cutoff by a smooth (Gaussian / Schwartz) window: the two families of operators that move a
window around phase space,

* **translation** `(T_a f)(t) = f (t - a)`,
* **modulation** `(M_b f)(t) = e^{2πi b t} f (t)`,

and the *modulation/translation identity* (the Weyl commutation relation) that they satisfy.

## Main results

* `modOp_transOp` — **Weyl commutation relation**: `M_b T_a = χ(b a) · T_a M_b`, where
  `χ(x) = e^{2πix}`.  Translation and modulation commute only up to the phase `e^{2πi ab}`; this
  failure of commutativity *is* the Heisenberg group.
* `Heis` — the (circle-valued) **Heisenberg group** with multiplication
  `(a,b,z)·(a',b',z') = (a+a', b+b', z z' χ(b a'))`, with a full `Group` instance proved from the
  cocycle identity.
* `heisRep` — the **Schrödinger/Gabor representation** `Heis →* Function.End (ℝ → ℂ)`,
  `(a,b,z) ↦ z · T_a M_b`: a genuine monoid homomorphism, i.e. the Weyl relation is exactly what
  makes the composite of two Gabor shifts a third one.
* `heisRep_injective` — the representation is **faithful**: the Gaussian is a test vector which
  separates all Heisenberg elements.  Consequently the phase factor in `modOp_transOp` cannot be
  removed by any renormalisation of the operators.
* `modOp_transOp_ne` — an adversarial check: the phase is really needed, the two orders of
  composition differ on any window that is nonzero at the origin.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).** Windowing should be an *action of a group*, not an ad hoc
  cutoff; the correct group is the Heisenberg group, and the rectangular window of the catalog is
  merely one (non-smooth) vector in a representation space.
* **Experiment (Experimenter).** All operator identities reduce to `Complex.exp_add` after
  clearing casts; the group axioms for `Heis` reduce to the cocycle identity
  `b·a' + (b+b')·a'' = b'·a'' + b·(a' + a'')`.  Faithfulness needed a genuinely analytic input:
  the Gaussian test vector is nowhere zero and has a unique maximum, which pins down `a`, then
  the phase `z`, then the modulation `b` via `χ(1/4) = i ≠ 1`.
* **Analysis (Analyst).** The phase cocycle `χ(ba')` is not a coboundary — faithfulness shows the
  central `Circle` factor is not redundant.  This is the structural reason a *smooth* window can
  be moved freely in phase space while keeping all of its algebraic bookkeeping exact.
* **Critique (Critic).** Nothing here is definitional: `modOp_transOp` is false without the phase
  (`modOp_transOp_ne`), and `heisRep_injective` shows the group is not a proper quotient.
-/

open SmoothWindows

open Complex Real

/-! ## The character `χ(x) = e^{2πix}` -/





@[simp]

theorem SmoothWindows.norm_chi(x : ℝ) : ‖chi x‖ = 1 := by sorry
