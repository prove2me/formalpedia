-- Prove2me | Definitions.Def_Cryptography_FactoringBarriers_ResourceClassification
-- name    : Cryptography_FactoringBarriers_ResourceClassification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T18:12:11.197131+00:00
-- url     : https://prove2.me/theorems/0abbbfca-1a34-49e5-9ea0-b8634ddd9581
-- title:
--   Aether Catalog definitions — Cryptography_FactoringBarriers_ResourceClassification
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.FactoringBarriers.ResourceClassification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/FactoringBarriers/ResourceClassification.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder
import Theorems.Thm_FactoringBarriers_Lfun_superpoly
import Theorems.Thm_FactoringBarriers_Superpoly_exp_linear

/-!
# Classification of Classical Factoring Resources and Their Barriers

Every *known* classical resource for attacking integer factorization comes with
a documented running-time barrier:

| resource      | representative algorithm | barrier (in `x = log N`)         |
|---------------|--------------------------|----------------------------------|
| randomness    | Pollard rho              | `exp (x/4)`  (i.e. `Θ(N^{1/4})`) |
| smoothness    | CFRAC / QS / GNFS        | `L[1/3, c]`                      |
| iteration     | Williams `p+1` / ECM     | `L[1/2, √2]` in `log p ≈ x/2`    |
| analog/chaos  | analog dynamics          | no structural gain: `L[1/3, c]`  |

This file formalises the classification as a finite type `ClassicalResource`
with an assigned `barrierCost`, and proves the two facts that make the
conditional-impossibility schema work:

* `barrierCost_superpoly` — **every** classified barrier is superpolynomial;
* `barrier_hierarchy` — the classification is non-degenerate: the randomness
  barrier is genuinely exponential while the smoothness/analog barriers are
  strictly subexponential, so the four entries are not a repackaging of one bound.

Note the honest scope: these are *definitions recording the known state of the
art*, together with real theorems about the growth of the recorded bounds.
Nothing here asserts that the table is exhaustive of all conceivable resources;
that is exactly the gap the capstone keeps explicit.
-/

namespace FactoringBarriers

open Filter Real
open scoped Topology

/-! ## Stability of superpolynomiality under linear rescaling of the input -/

/-- If `f` is superpolynomial then so is `x ↦ f (x / b)` for any `b > 0`.
This is needed because the ECM barrier is stated in `log p`, not `log N`. -/
theorem Superpoly.comp_div {f : ℝ → ℝ} (hf : Superpoly f) {b : ℝ} (hb : 0 < b) :
    Superpoly (fun x => f (x / b)) := by
  intro d
  have hdiv : Tendsto (fun x : ℝ => x / b) atTop atTop :=
    Filter.Tendsto.atTop_div_const hb tendsto_id
  have h1 : Tendsto (fun x : ℝ => f (x / b) / (x / b) ^ d) atTop atTop :=
    (hf d).comp hdiv
  have hbd : (0:ℝ) < b ^ d := Real.rpow_pos_of_pos hb d
  have h2 : Tendsto (fun x : ℝ => (f (x / b) / (x / b) ^ d) / b ^ d) atTop atTop :=
    Filter.Tendsto.atTop_div_const hbd h1
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.div_rpow hx.le hb.le]
  field_simp

/-! ## The four classified resources -/

/-- The four classified classical resources for circumventing the structural
barrier in factoring. -/
inductive ClassicalResource
  | randomness
  | smoothness
  | iteration
  | analog
  deriving DecidableEq, Repr

/-- The documented running-time barrier attached to each classified resource,
expressed as a function of the bit-size parameter `x = log N`. -/
noncomputable def barrierCost : ClassicalResource → (ℝ → ℝ)
  | .randomness => fun x => Real.exp (1 / 4 * x)
  | .smoothness => Lfun (1 / 3) 1
  | .iteration => fun x => Lfun (1 / 2) (Real.sqrt 2) (x / 2)
  | .analog => Lfun (1 / 3) 1

/-! ## Every classified barrier is superpolynomial -/

/-- **Barrier theorem.** For each of the four classified resources, the
associated running-time barrier grows faster than every polynomial in the
bit-size `log N`. -/
theorem barrierCost_superpoly (rho : ClassicalResource) : Superpoly (barrierCost rho) := by
  cases rho with
  | randomness => exact Superpoly_exp_linear (by norm_num)
  | smoothness => exact Lfun_superpoly (by norm_num) (by norm_num) (by norm_num)
  | iteration =>
      have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      exact (Lfun_superpoly hs (by norm_num) (by norm_num)).comp_div (by norm_num)
  | analog => exact Lfun_superpoly (by norm_num) (by norm_num) (by norm_num)


/-! ## The classification is non-degenerate -/




end FactoringBarriers


