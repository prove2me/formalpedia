-- Prove2me | Theorems.Thm_ZeroOneExpansion_theorem_14
-- name    : ZeroOneExpansion.theorem_14
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:22:38.545054+00:00
-- url     : https://prove2.me/theorems/fbf67d4d-4687-4cb5-ad81-4fe7a3d8203d
-- title:
--   Theorem 14 — $h(G_n)\le 4n\beta^n/(1-\beta^n)$ with $\beta=(1+\sqrt6)^2/12<1$
-- statement:
--   Let $\beta=(1+\sqrt6)^2/12$. Then:
--
--   1. $\beta<1$;
--   2. for every $n\ge1$, $$h(G_n)\le\frac{4n\beta^n}{1-\beta^n};$$
--   3. $h(G_n)<1$ for all sufficiently large $n$;
--   4. there is a constant $c>0$ such that $h(G_n)\le\exp(-c\dim(P_n))$ for all sufficiently large $n$.
--
--   This is the explicit form of Theorem 1 for the family $P_n$.
--
--   Differences from the source:
--   - encoding: h(G) as a minimum of real numbers → edgeExpansion : EReal, the infimum over admissible S, ⊤ when no S is admissible; reason: for a finite graph with an admissible set it is the minimum; ⊤ makes an upper bound on h non-vacuous
--   - encoding: G_n = (V_n, E_n), the 1-skeleton of P_n → Gn n = Grunbaum2003.polytopeGraph (Pn n); reason: distinct vertices in a common one-dimensional exposed face, the paper's G(P)
--   - encoding: dim(P) = dim(aff(P)) → polyDim P = Module.finrank ℝ (affineSpan ℝ P).direction; reason: the dimension of the affine hull
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Theorem 14, display (4), p.9

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn
import Definitions.Def_ZeroOneExpansion_polyDim
import Definitions.Def_ZeroOneExpansion_edgeExpansion

set_option autoImplicit false

namespace ZeroOneExpansion

/-- **Theorem 14** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.9). Let `β := (1 + √6)^2 / 12 < 1`. For every `n ≥ 1`,
`h(Gn) ≤ 4nβ^n / (1 − β^n)` (display (4)). In particular `h(Gn) < 1` for all sufficiently large `n`.
Moreover `h(Gn) ≤ exp(−c dim(Pn))` for some constant `c > 0` and all sufficiently large `n`.

**Formalization Note** `h` is `edgeExpansion` (`EReal`-valued, `⊤` if no set is admissible), and
real bounds are coerced to `EReal`. `dim` is `polyDim`. The constant `c` is chosen before "for all
sufficiently large `n`" (`∀ᶠ n in atTop`), so it does not depend on `n`. -/
theorem theorem_14 :
    let β : ℝ := (1 + Real.sqrt 6) ^ 2 / 12
    β < 1 ∧
    (∀ n : ℕ, 1 ≤ n →
      edgeExpansion (Gn n) ≤ (((4 * n * β ^ n / (1 - β ^ n) : ℝ)) : EReal)) ∧
    (∀ᶠ n in Filter.atTop, edgeExpansion (Gn n) < 1) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop,
      edgeExpansion (Gn n) ≤ ((Real.exp (-c * (polyDim (Pn n) : ℝ)) : ℝ) : EReal) := by sorry

end ZeroOneExpansion
