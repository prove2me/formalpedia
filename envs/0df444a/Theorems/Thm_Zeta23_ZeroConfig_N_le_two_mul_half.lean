-- Prove2me | Theorems.Thm_Zeta23_ZeroConfig_N_le_two_mul_half
-- name    : Zeta23.ZeroConfig.N_le_two_mul_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:42:05.222329+00:00
-- url     : https://prove2.me/theorems/1b3e6640-c1e5-4258-a074-41683e4227eb
-- title:
--   Reflection halving: $N(T_1,T_2) \le 2 \sum_{\beta \ge 1/2} m_\rho$
-- statement:
--   Let $Z$ be an abstract zero configuration (`ZeroConfig`: distinct points $\rho = \beta + i\gamma$ in the strip $0 \le \beta \le 1$ with multiplicities $m_\rho \ge 1$, invariant under the reflection $\rho \mapsto 1 - \bar\rho$ with equal multiplicities, locally finite). For reals $T_1, T_2$, the window is the set of $\rho \in Z$ with $T_1 < \gamma \le T_2$, and $N(T_1, T_2) = \sum_{\rho \in \mathrm{window}} m_\rho$ counts them with multiplicity.
--
--   **Statement.** As real numbers,
--   $$N(T_1, T_2) \;\le\; 2 \sum_{\substack{\rho \in \mathrm{window} \\ \operatorname{Re}\rho \ge 1/2}} m_\rho$$
--   (the right-hand sum is a finite `finsum` over the window intersected with $\{\operatorname{Re}\rho \ge 1/2\}$). The reflection $\rho \mapsto 1 - \bar\rho$ preserves the ordinate and the multiplicity and maps the zeros with $\beta < 1/2$ injectively into those with $\beta > 1/2$, so the right half of the strip carries at least half the count.
--
--   **Role.** In the module `Zeta23.RvM.Halving` this is used by `Zeta23.RvM.zeta_local_zero_count`: it lets the Jensen-disc zero count cover only the half-strip $\sigma \ge 1/2$, so that $\zeta$ is never evaluated left of $\sigma = 0.19$ and no functional-equation growth estimates are needed.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/Halving.lean#L42-L84

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

open Set
open Zeta23
open ZeroConfig
variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

theorem Zeta23.ZeroConfig.N_le_two_mul_half :
    (Z.N T₁ T₂ : ℝ) ≤ 2 * ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ {ρ | 1 / 2 ≤ ρ.re}, (Z.mult ρ : ℝ) := by sorry
