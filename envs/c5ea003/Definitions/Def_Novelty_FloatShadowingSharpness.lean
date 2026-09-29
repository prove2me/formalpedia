-- Prove2me | Definitions.Def_Novelty_FloatShadowingSharpness
-- name    : Novelty_FloatShadowingSharpness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:26:55.348231+00:00
-- url     : https://prove2.me/theorems/7bebcff5-b36f-4f36-9559-008367523086
-- title:
--   Aether Catalog definitions — Novelty_FloatShadowingSharpness
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FloatShadowingSharpness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FloatShadowingSharpness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing

/-!
# Nonautonomous shadowing bounds and their sharpness

Third cycle of the programme.  Two questions left open by the previous cycles
are settled here.

1. *Is the uniform Lipschitz constant necessary?*  No: `variable_shadowing`
   replaces `L` by the observed, step-dependent local expansion factors `L n`,
   producing the a-posteriori error recursion `E 0 = 0`,
   `E (n+1) = δ + L n · E n`.  Specialising to a constant sequence recovers the
   geometric bound (`errBound_const`), so the nonautonomous statement is a
   strict refinement.

2. *Is the exponential growth of the forward bound an artifact of the proof?*
   No: `finite_shadowing_sharp` exhibits, for every `L ≥ 0` and `δ ≥ 0`, an
   `L`-Lipschitz map and a `δ`-pseudo-orbit for which the distance to the true
   orbit **equals** `δ (1 + L + ⋯ + L^{n-1})` at every step.  Hence the forward
   shadowing theorem of the first cycle cannot be improved, and the improvement
   obtained in the second cycle (`expanding_backward_shadowing`) genuinely
   requires moving the initial condition.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the geometric factor in forward shadowing is exactly
attained by the linear map `z ↦ L z` driven by a constant defect `δ`, so no
proof technique can remove it while keeping the initial point fixed.
Experiment (Experimenter): the witness is the affine recursion
`x_{n+1} = L xₙ + δ` started at `0`, whose true orbit is identically `0`; the
distance is the geometric sum, verified by induction (`sharpWitness_eq`).
Analysis (Analyst): the three cycles now separate cleanly:
semantics (`O(u)` defect) → forward dynamics (`O(u · Lⁿ)`, sharp) →
backward dynamics under expansivity (`O(u)`, uniform in n).
Critique (Critic): the sharpness witness is an honest pseudo-orbit — its defect
is exactly `δ` at every step, not merely bounded by `δ` — and the map is exactly
`L`-Lipschitz, so no slack is hidden in the hypotheses.
-- !-- End Lab Notes -- !--
-/

namespace Novelty.FloatBackwardError

open scoped BigOperators

/-- The a-posteriori error recursion driven by the observed local expansion
factors: `E 0 = 0`, `E (n+1) = δ + L n · E n`. -/
def errBound (δ : ℝ) (L : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => δ + L n * errBound δ L n




/-! ### Sharpness of the forward shadowing bound -/

/-- The extremal pseudo-orbit `x₀ = 0`, `x_{n+1} = L xₙ + δ`. -/
def sharpWitness (L δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => L * sharpWitness L δ n + δ




/-! ### The a-posteriori bound for a binary64 logistic execution -/




end Novelty.FloatBackwardError


