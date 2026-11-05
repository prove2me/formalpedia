-- Prove2me | Theorems.Thm_ZhangCFL_theorem_3_3
-- name    : ZhangCFL.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:02.863019+00:00
-- url     : https://prove2.me/theorems/8677c34c-d8e4-462d-aae1-64742331d143
-- title:
--   Theorem 3.3: variational formulas (3.1) and (3.2) for $\operatorname{Tr}|XY|^{r}$
-- statement:
--   Let $r_0,r_1,r_2>0$ satisfy $\frac1{r_0}=\frac1{r_1}+\frac1{r_2}$, and let $X,Y$ be invertible complex matrices of the same size. Writing $\operatorname{Tr}|M|^r=\operatorname{Tr}(M^*M)^{r/2}$,
--
--   $$
--   \operatorname{Tr}|XY|^{r_0} = \min_{Z\ \text{invertible}}\Big\{\frac{r_0}{r_1}\operatorname{Tr}|XZ|^{r_1}+\frac{r_0}{r_2}\operatorname{Tr}|Z^{-1}Y|^{r_2}\Big\} \qquad (3.1)
--   $$
--
--   and
--
--   $$
--   \operatorname{Tr}|XY|^{r_1} = \max_{Z\ \text{invertible}}\Big\{\frac{r_1}{r_0}\operatorname{Tr}|XZ|^{r_0}-\frac{r_1}{r_2}\operatorname{Tr}|Y^{-1}Z|^{r_2}\Big\}. \qquad (3.2)
--   $$
--
--   Both the minimum and the maximum are attained. These two formulas are the variational method of the paper: combined with Lemma 3.2, they reduce Theorem 1.1 to Theorem 3.5 and Theorem 3.5 to Theorem 3.7.
--
--   **Formalization Note** $\operatorname{Tr}|M|^r$ is `ZhangCFL.trAbsPow r M`. "min" and "max" are `IsLeast` and `IsGreatest` of the set of values of the bracket over all invertible $Z$ (not only positive ones). $Z^{-1}$, $Y^{-1}$ are matrix inverses.
--
--   Differences from the source:
--   - encoding: min and max over Z ∈ B(H)^× → IsLeast and IsGreatest of the set of bracket values over invertible matrices Z; reason: this is the statement that the extremum exists, is attained and equals the left side
--   - encoding: Tr|M|^r → ZhangCFL.trAbsPow r M = real part of Tr (M*M)^{r/2}; reason: |M| = (M*M)^{1/2} as on p.4, and the trace of a positive semidefinite matrix is real
--   - encoding: operators on a finite-dimensional Hilbert space H and B(H)^× → complex matrices indexed by a finite type and IsUnit; reason: the same objects in a chosen basis
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, Theorem 3.3, eqs. (3.1) and (3.2), p.8 (proof pp.8–9)

import Mathlib
import Definitions.Def_ZhangCFL_trAbsPow

namespace ZhangCFL

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, Theorem 3.3, eqs. (3.1) and (3.2), p.8: for `r_i > 0`, `i = 0, 1, 2`, with
`1/r₀ = 1/r₁ + 1/r₂`, and any invertible `X, Y`,
(3.1) `Tr|XY|^{r₀} = min_{Z invertible} { (r₀/r₁) Tr|XZ|^{r₁} + (r₀/r₂) Tr|Z⁻¹Y|^{r₂} }`,
(3.2) `Tr|XY|^{r₁} = max_{Z invertible} { (r₁/r₀) Tr|XZ|^{r₀} − (r₁/r₂) Tr|Y⁻¹Z|^{r₂} }`.

**Formalization Note.** `Tr|M|^r` is `ZhangCFL.trAbsPow r M = Tr (M* M)^{r/2}`. "min"/"max"
mean attained: the left side is `IsLeast`/`IsGreatest` of the set of values of the bracket over
all invertible `Z` (not only positive ones). `⁻¹` is the matrix inverse. -/
theorem theorem_3_3 {n : Type} [Fintype n] [DecidableEq n]
    (r₀ r₁ r₂ : ℝ) (h₀ : 0 < r₀) (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hr : 1 / r₀ = 1 / r₁ + 1 / r₂)
    (X Y : Matrix n n ℂ) (hX : IsUnit X) (hY : IsUnit Y) :
    IsLeast {v : ℝ | ∃ Z : Matrix n n ℂ, IsUnit Z ∧
        v = r₀ / r₁ * trAbsPow r₁ (X * Z) + r₀ / r₂ * trAbsPow r₂ (Z⁻¹ * Y)}
      (trAbsPow r₀ (X * Y)) ∧
    IsGreatest {v : ℝ | ∃ Z : Matrix n n ℂ, IsUnit Z ∧
        v = r₁ / r₀ * trAbsPow r₀ (X * Z) - r₁ / r₂ * trAbsPow r₂ (Y⁻¹ * Z)}
      (trAbsPow r₁ (X * Y)) := by sorry

end ZhangCFL
