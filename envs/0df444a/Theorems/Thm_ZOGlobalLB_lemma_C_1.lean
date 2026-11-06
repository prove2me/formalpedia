-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_C_1
-- name    : ZOGlobalLB.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:49:07.397972+00:00
-- url     : https://prove2.me/theorems/97be2107-1118-48d9-ad46-f82b899c5012
-- title:
--   Lemma C.1 — a fixed regular version of each field
-- statement:
--   Let the tensors of one label be independent standard Gaussians and $\sigma>0$. The series (85) defines a field $Q(q,g)$ that is jointly measurable in the tensors and the query. Almost surely:
--
--   1. $Q$ is $C^1$ on the open neighbourhood $\{|g|<2\}$ of the query strip $\mathbb R^m\times[0,1]$;
--   2. the finite tensor sums and their first derivatives converge to $Q$ and its first derivative uniformly on the strip.
--
--   Moreover the global Lipschitz constant of $Q$ on the strip has finite second moment.
--
--   Each label keeps this one sample function at all adaptive and repeated queries, which is what the reuse analysis requires.
--
--   Differences from the source:
--   - generalization: C¹ on the query strip ℝᵐ × [0,1] → C¹ on the open set {|g| < 2}; reason: the proof (p.47) obtains it there; specializes to the strip with its endpoints
--   - encoding: the version of the series → the tsum of the series (0 where not summable); reason: agrees with the paper's version except on a null event
--   - reading: each label retains this same version at all queries → no clause; replies of a label always read the same array; reason: holds by construction
--   - encoding: Lipschitz constant on the strip, finite second moment → lipConst of the restriction to the strip; ∫⁻ lipConst² < ⊤; reason: same quantity in [0,∞]
--   - encoding: degrees ℓ ≥ 1 → index ℓ : ℕ standing for degree ℓ + 1; reason: Lean convention
--   - reading: value and first derivatives are simultaneous limits of the finite tensor sums → almost surely, the partial sums and their Fréchet derivatives converge uniformly on the strip; reason: the proof (pp.45–47) obtains uniform convergence, and p.47 states it
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma C.1, p.45; proof p.47

import Mathlib
import Definitions.Def_ZOGlobalLB_lipConst
import Definitions.Def_ZOGlobalLB_Field

open MeasureTheory Filter
open scoped ENNReal

namespace ZOGlobalLB

/-- **Lemma C.1 (A fixed regular version of each field).** Xia, Yuan, arXiv:2610.19652,
Lemma C.1, p.45.

Let the tensors `G` of one label be independent standard Gaussian (law `gaussArr (Idx m)`) and
`σ > 0`. The series (85) defines a jointly measurable version whose samples are `C¹` on the query
strip `ℝᵐ × [0, 1]`. Its value and first derivatives are simultaneous limits of the finite tensor
sums. Its global Lipschitz constant on the strip has finite second moment.

**Formalization Note.**
* Jointly measurable: `(G, q, g) ↦ Q(q, g)` is measurable on the product of the array space and
  the query space.
* `C¹` on the strip is stated on the open neighbourhood `{|g| < 2}` of the strip, as the proof
  does (p.47: "the derivative convergence also holds on an open neighborhood of the query strip,
  including its endpoints"); this specializes to the closed strip with its endpoints.
* The limits are uniform on the strip, almost surely: values of `Qpartial` and their Fréchet
  derivatives converge to those of `Qfield`.
* "Each label retains this same version at all adaptive and repeated queries" holds by
  construction: a label's reply at any query reads the same array `G` (see `OneStageRule.replies`).
* The Lipschitz constant on the strip is `lipConst` of the restriction to the strip, in `ℝ≥0∞`;
  finite second moment is `∫⁻ lipConst² < ⊤`. -/
theorem lemma_C_1 {m : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    Measurable (fun p : (Idx m → ℝ) × (E m × ℝ) => Qfield σ p.1 p.2.1 p.2.2) ∧
    (∀ᵐ G ∂(gaussArr (Idx m)),
      ContDiffOn ℝ 1 (QfieldP σ G) {p | |p.ofLp.2| < 2} ∧
      TendstoUniformlyOn (fun L => QpartialP σ G L) (QfieldP σ G) atTop (strip m) ∧
      TendstoUniformlyOn (fun L => fderiv ℝ (QpartialP σ G L)) (fderiv ℝ (QfieldP σ G)) atTop
        (strip m)) ∧
    ∫⁻ G, lipConst (fun p : strip m => QfieldP σ G p) ^ 2 ∂(gaussArr (Idx m)) < ⊤ := by sorry

end ZOGlobalLB
