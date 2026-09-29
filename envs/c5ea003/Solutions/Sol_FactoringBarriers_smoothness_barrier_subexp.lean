-- Prove2me | solution 1 for FactoringBarriers.smoothness_barrier_subexp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:31:50.031022+00:00
-- url     : https://prove2.me/submissions/0a6ddfad-d506-4cd9-a50b-93b865ed43ab

-- Sol generated from Cryptography/FactoringBarriers/ResourceClassification.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder
import Definitions.Def_Cryptography_FactoringBarriers_ResourceClassification
import Theorems.Thm_FactoringBarriers_Lfun_subexp

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

open FactoringBarriers

open Filter Real
open scoped Topology

/-! ## Stability of superpolynomiality under linear rescaling of the input -/


/-! ## The four classified resources -/



/-! ## Every classified barrier is superpolynomial -/



/-! ## The classification is non-degenerate -/





open FactoringBarriers in
theorem solution: Subexp (barrierCost .smoothness) :=
  Lfun_subexp (by norm_num) (by norm_num)
