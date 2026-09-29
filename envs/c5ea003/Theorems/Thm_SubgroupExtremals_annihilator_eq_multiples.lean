-- Prove2me | Theorems.Thm_SubgroupExtremals_annihilator_eq_multiples
-- name    : SubgroupExtremals.annihilator_eq_multiples
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:14:12.995226+00:00
-- url     : https://prove2.me/theorems/c8ff0675-3abc-45c7-8fd1-ba2480e610c9
-- title:
--   The annihilator of the subgroup of multiples of `d` is the subgroup of multiples of `m`.
-- statement:
--   The annihilator of the subgroup of multiples of `d` is the subgroup of multiples of `m`.
--
--   ```lean
--   theorem SubgroupExtremals.annihilator_eq_multiples:
--       (Finset.univ.filter fun k : ZMod (d * m) => (d : ZMod (d * m)) * k = 0)
--         = (Finset.range d).image (fun t => ((m * t : ℕ) : ZMod (d * m))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/SubgroupExtremals.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/SubgroupExtremals.lean#L166

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




/-! ## The indicator of a subgroup and its Fourier transform -/


variable (d m : ℕ) [NeZero d] [NeZero m]




variable {d m}

theorem SubgroupExtremals.annihilator_eq_multiples:
    (Finset.univ.filter fun k : ZMod (d * m) => (d : ZMod (d * m)) * k = 0)
      = (Finset.range d).image (fun t => ((m * t : ℕ) : ZMod (d * m))) := by sorry
