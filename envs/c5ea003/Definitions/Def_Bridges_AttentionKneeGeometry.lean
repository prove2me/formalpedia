-- Prove2me | Definitions.Def_Bridges_AttentionKneeGeometry
-- name    : Bridges_AttentionKneeGeometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:12:20.995884+00:00
-- url     : https://prove2.me/theorems/0931b548-6fe0-4e7f-b1b6-813ba2d478b9
-- title:
--   Aether Catalog definitions — Bridges_AttentionKneeGeometry
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AttentionKneeGeometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AttentionKneeGeometry.lean by skeleton subtraction
import Mathlib
/-
  # The geometry of the retention knee: top-`k` attention mass, grids, and budgets

  ## Bridge: discrete convexity / majorization  ↔  limited-memory deployment tables

  This module gives a formal, assumption-explicit theory of the object that the
  NET-63 experiment series measures: the **retention knee**

      `k*(g) = least k such that the mass retained by the k largest keys is ≥ g`.

  The empirical thread (paper 148, round 16, "THE-2048-KNEE-IS-TWENTY-FOUR")
  reports, at context 2048 on corpus-A, gate `g = 0.98`, averaged over 12 windows:

      | k        | 20     | 24     | 28     | 32     |
      | retained | 0.9793 | 0.9835 | 0.9854 | 0.9885 |

  and the deployment chain `k* = 16, 20, 24` at contexts `512, 1024, 2048`,
  all inside a ~30-key budget.

  What we prove here (all statements are about an arbitrary nonnegative weight
  profile `w : ℕ → ℝ`, `mass w k = ∑_{i<k} w i`; when `w` is *antitone* this is
  exactly the top-`k` mass of a sorted attention row):

  * `knee` well-posedness: `knee_pass`, `knee_le_of_pass`, `mass_lt_of_lt_knee`,
    and the two-sided characterisation `pass_iff_knee_le`.
  * `knee_eq_of_fail_pass`: the "fail at `k-1`, pass at `k`" certificate that a
    sweep actually produces.
  * **Grid geometry.** A sweep only ever reports `gridKnee G`, the least *grid*
    point that passes.  We prove `knee_le_gridKnee` (a sweep never
    under-reports), `gridKnee_refine` (refining the grid can only *lower* the
    reported knee — the exact mechanism by which "28" became "24"), and
    `gridKnee_eq_knee_of_mem` (ON-grid landing).  `knee_bracket` turns the two
    numbers `0.9793 ✗ / 0.9835 ✓` into the sharp bracket `20 < k* ≤ 24`.
  * **Majorization ⇒ knee monotonicity.** If lengthening the context spreads the
    attention mass (`mass v k ≤ mass w k` for all `k`, i.e. `w` majorizes `v` in
    the partial-sum order) then `knee w g ≤ knee v g`, with a strict version
    `knee_lt_of_majorize_strict`.  This is the structural reason a chain like
    `16 < 20 < 24` is forced rather than coincidental (`deployment_chain`).
  * **Geometric tails ⇒ a finite key budget.** `knee_le_of_geometric_tail` and
    `exists_budget_of_geometric_tail`: an exponentially decaying attention tail
    always has a finite knee, with an explicit `C rᴺ ≤ 1 - g` certificate, and
    `knee_le_thirty_of_geometric_tail` is the "~30 keys" budget statement.
  * **An adversarial (Critic-stage) finding.** For antitone `w`, `mass` is
    *discretely concave*: equal-width block increments are antitone
    (`block_increment_antitone`), and averaging over windows preserves this
    (`avgMass_block_concave`).  The reported fine-grid row at 2048 **violates**
    this: `0.9854 - 0.9835 = 0.0019 < 0.0031 = 0.9885 - 0.9854`.  Hence
    `net63_fine2048_not_window_averaged_topk`: those four numbers cannot be the
    window-averaged top-`k` masses of any family of sorted attention rows.  The
    *knee* conclusion `k* = 24` survives (it only uses monotonicity), but the
    concavity-based extrapolation to `k = 28, 32` does not.

  * **Mixtures.**  `knee_mixture_le_max`: a convex blend of two heads never
    needs more keys than the harder of the two, so a multi-head budget is
    controlled by the worst head rather than by their sum.

  Everything is proved from scratch over `ℝ`; the concrete geometric example
  `geometricProfile` at the end exhibits a genuine coarse-grid overestimate
  (`geometric_coarse_grid_overestimates`: true knee 6, coarse grid reports 8).
-/


namespace Bridges.AttentionKneeGeometry

open Finset

/-! ## 1. Retained mass -/

/-- `mass w k` is the attention mass retained by the first `k` keys of the
weight profile `w`.  When `w` is antitone this is the top-`k` mass. -/
def mass (w : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, w i






/-! ## 2. The knee -/

/-- `knee w g` is the least number of keys whose retained mass meets the gate `g`
(and `0` if the gate is never met). -/
noncomputable def knee (w : ℕ → ℝ) (g : ℝ) : ℕ := sInf {k | g ≤ mass w k}








/-! ## 3. Majorization: why the deployment chain is monotone -/



/-! ## 4. Grid geometry: what a sweep can and cannot report -/

/-- The knee **as reported by a sweep over the finite grid `G`**: the least grid
point that passes the gate. -/
noncomputable def gridKnee (G : Set ℕ) (w : ℕ → ℝ) (g : ℝ) : ℕ :=
  sInf {k | k ∈ G ∧ g ≤ mass w k}









/-! ## 5. Geometric tails and the key budget -/




/-! ## 6. Window averaging, and an obstruction -/

/-- The window-averaged retention curve of a family of `m` attention rows. -/
noncomputable def avgMass (m : ℕ) (W : Fin m → ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ j, mass (W j) k) / m


/-! ### The NET-63 round-16 fine grid at context 2048

Reported (12 windows, gate `g = 0.98`, corpus-A):
`R 20 = 0.9793`, `R 24 = 0.9835`, `R 28 = 0.9854`, `R 32 = 0.9885`.
-/

/-- The reported fine-grid row at context 2048. -/
def net63R : ℕ → ℝ
  | 20 => 0.9793
  | 24 => 0.9835
  | 28 => 0.9854
  | 32 => 0.9885
  | _  => 0





/-! ## 7. The deployment chain `16 < 20 < 24` -/



/-! ## 8. A concrete coarse-grid overestimate -/

/-- The dyadic attention profile `w i = 2^{-(i+1)}` (antitone, total mass 1). -/
noncomputable def geometricProfile : ℕ → ℝ := fun i => (1 / 2) ^ (i + 1)






/-! ## 9. Non-vacuity: the deployment hypotheses are realizable -/

/-- The step (plateau) profile: mass `c` on each of the first `K` keys. -/
def stepProfile (K : ℕ) (c : ℝ) : ℕ → ℝ := fun i => if i < K then c else 0









/-! ## 10. Mixtures: multi-head budgets -/



/-!
## Lab Notes (experimental data used)

* NET-63 round 16, corpus-A, context 2048, gate `0.98` exact, 12 windows:
  `k = 20 → 0.9793 ✗`, `k = 24 → 0.9835 ✓`, `k = 28 → 0.9854 ✓`,
  `k = 32 → 0.9885 ✓`.  Formalised in `net63R`.
* Deployment chain: knees `16, 20, 24` at contexts `512, 1024, 2048`
  (`deployment_chain`).
* Derived facts: margin at 24 is `+0.0035` = five times the deficit at 20
  (`net63_margin_ratio`); the knee is bracketed by `20 < k* ≤ 24`
  (`net63_knee_bracket`).
* Negative finding: the four reported numbers are not window-averaged top-`k`
  masses of sorted rows (`net63_fine2048_not_window_averaged_topk`), because
  `0.9854 - 0.9835 = 0.0019 < 0.0031 = 0.9885 - 0.9854` breaks discrete
  concavity.
-/

end Bridges.AttentionKneeGeometry


