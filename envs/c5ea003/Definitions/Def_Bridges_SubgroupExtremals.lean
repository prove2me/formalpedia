-- Prove2me | Definitions.Def_Bridges_SubgroupExtremals
-- name    : Bridges_SubgroupExtremals
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:40.162421+00:00
-- url     : https://prove2.me/theorems/84bf21c5-1de2-48e0-8e56-aa120deecc95
-- title:
--   Aether Catalog definitions — Bridges_SubgroupExtremals
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SubgroupExtremals`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SubgroupExtremals.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty

/-!
# Subgroup indicators are the extremals of the Donoho–Stark bound

The previous file proved the Donoho–Stark uncertainty principle
`N ≤ |supp Φ| * |supp 𝓕Φ|` on `ZMod N`, showed it is attained by delta functions, and exhibited
one composite counterexample (`N = 4`) to the additive prime bound. This file proves the general
structural statement behind that counterexample.

For every factorisation `N = d * m` the indicator function of the subgroup of multiples of `d`
has support of size `m`, and its discrete Fourier transform is the indicator of the subgroup of
multiples of `m` scaled by `m`, hence has support of size `d`. Consequently:

* `SubgroupExtremals.donoho_stark_extremal` : the Donoho–Stark bound is attained with equality by
  the whole family of subgroup indicators, `|supp Φ| * |supp 𝓕Φ| = N`;
* `SubgroupExtremals.additive_bound_le_divisor_sum` : the additive support sum equals `d + m`,
  so the prime (Tao) bound `N + 1` fails for every composite `N`;
* `SubgroupExtremals.tao_bound_fails_of_composite` : an explicit statement of that failure.

The proof is a genuine finite Fourier computation: the transform of the indicator is a geometric
sum of a root of unity, which vanishes off the annihilator subgroup.
-/

open Finset ZMod FourierUncertainty

namespace SubgroupExtremals

/-! ## Counting the multiples of `a` in `ZMod (a * b)` -/

section Counting

variable {N a b : ℕ} [NeZero N]



end Counting

/-! ## The indicator of a subgroup and its Fourier transform -/

section Indicator

variable (d m : ℕ) [NeZero d] [NeZero m]

instance neZero_mul : NeZero (d * m) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne m)⟩

/-- The subgroup of multiples of `d` inside `ZMod (d * m)`; it has `m` elements. -/
noncomputable def multiples : Finset (ZMod (d * m)) :=
  (Finset.range m).image (fun t => ((d * t : ℕ) : ZMod (d * m)))

open scoped Classical in
/-- The indicator function of the subgroup of multiples of `d`. -/
noncomputable def indicator : ZMod (d * m) → ℂ :=
  fun j => if j ∈ multiples d m then 1 else 0

variable {d m}














end Indicator

end SubgroupExtremals


