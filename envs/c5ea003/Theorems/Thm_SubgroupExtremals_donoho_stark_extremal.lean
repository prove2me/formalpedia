-- Prove2me | Theorems.Thm_SubgroupExtremals_donoho_stark_extremal
-- name    : SubgroupExtremals.donoho_stark_extremal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:14:50.103283+00:00
-- url     : https://prove2.me/theorems/b96bd074-59d1-4681-9e68-400d7670e956
-- title:
--   The Donoho–Stark bound is attained by every subgroup indicator.
-- statement:
--   **The Donoho–Stark bound is attained by every subgroup indicator.** For each factorisation
--   `N = d * m` the indicator of the multiples of `d` satisfies `|supp Φ| * |supp 𝓕Φ| = N`. Delta
--   functions are the case `d = N`, `m = 1`.
--
--   ```lean
--   theorem SubgroupExtremals.donoho_stark_extremal:
--       (fsupport (indicator d m)).card * (fsupport (𝓕 (indicator d m))).card = d * m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/SubgroupExtremals.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/SubgroupExtremals.lean#L210

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

theorem SubgroupExtremals.donoho_stark_extremal:
    (fsupport (indicator d m)).card * (fsupport (𝓕 (indicator d m))).card = d * m := by sorry
