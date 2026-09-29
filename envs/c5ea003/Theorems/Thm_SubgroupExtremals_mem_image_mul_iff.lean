-- Prove2me | Theorems.Thm_SubgroupExtremals_mem_image_mul_iff
-- name    : SubgroupExtremals.mem_image_mul_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:14:10.925956+00:00
-- url     : https://prove2.me/theorems/6e3ebfe6-5778-4405-9ab1-8c9bc49c3041
-- title:
--   Membership in the set of multiples of `a` is divisibility of the representative.
-- statement:
--   Membership in the set of multiples of `a` is divisibility of the representative.
--
--   ```lean
--   theorem SubgroupExtremals.mem_image_mul_iff(ha : a ≠ 0) (hN : N = a * b) (j : ZMod N) :
--       j ∈ (Finset.range b).image (fun t => ((a * t : ℕ) : ZMod N)) ↔ a ∣ j.val := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/SubgroupExtremals.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/SubgroupExtremals.lean#L34

-- Thm stub generated from Bridges/SubgroupExtremals.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Definitions.Def_Bridges_SubgroupExtremals

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

open SubgroupExtremals

/-! ## Counting the multiples of `a` in `ZMod (a * b)` -/


variable {N a b : ℕ} [NeZero N]

theorem SubgroupExtremals.mem_image_mul_iff(ha : a ≠ 0) (hN : N = a * b) (j : ZMod N) :
    j ∈ (Finset.range b).image (fun t => ((a * t : ℕ) : ZMod N)) ↔ a ∣ j.val := by sorry
