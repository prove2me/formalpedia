-- Prove2me | Theorems.Thm_ZeroOneExpansion_theorem_1
-- name    : ZeroOneExpansion.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:52.805981+00:00
-- url     : https://prove2.me/theorems/74942c81-3bb7-48ed-bc2a-72f61173ae2d
-- title:
--   Theorem 1 — full-dimensional 0/1-polytopes with exponentially small edge expansion
-- statement:
--   There exist a constant $c>0$ and an infinite sequence $(P_n)_{n\ge1}$ of full-dimensional 0/1-polytopes, with $\dim(P_n)\to\infty$, such that for all sufficiently large $n$
--   $$h(G(P_n))\le\exp\big(-c\dim(P_n)\big),$$
--   and in particular $h(G(P_n))<1$ for all sufficiently large $n$. Here $G(P)$ is the graph (1-skeleton) of $P$ and $h$ is the edge expansion.
--
--   This disproves the Mihail–Vazirani conjecture that $h(G(P))\ge1$ for every 0/1-polytope $P$, and also its weakening to an inverse-polynomial lower bound in the dimension.
--
--   Differences from the source:
--   - encoding: h(G) as a minimum of real numbers → edgeExpansion : EReal, the infimum over admissible S, ⊤ when no S is admissible; reason: for a finite graph with an admissible set it is the minimum; ⊤ makes an upper bound on h non-vacuous
--   - encoding: a sequence (P_n)_{n≥1} → a sequence indexed by ℕ, P n ⊆ ℝ^{d n}, with the 0/1 and full-dimensional properties required for n ≥ 1; reason: the term at n = 0 is irrelevant to dim → ∞ and to the eventual clauses
--   - encoding: G(P), the graph of P → Grunbaum2003.polytopeGraph (P n); reason: distinct vertices in a common one-dimensional exposed face, the paper's G(P)
--   - encoding: dim(P) = dim(aff(P)) → polyDim P = Module.finrank ℝ (affineSpan ℝ P).direction; reason: the dimension of the affine hull
--   - encoding: full-dimensional 0/1-polytope → IsZeroOnePolytope (P n) ∧ Grunbaum2003.IsDPolytope (P n) (a finite nonempty hull with affineSpan = ⊤); reason: full dimension is affine hull = ℝ^d
--   - encoding: dimensions tending to infinity → Filter.Tendsto (fun n => polyDim (P n)) atTop atTop; reason: the same limit
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Theorem 1, p.1

import Mathlib
import Definitions.Def_Grunbaum2003_polytopeGraph
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_ZeroOneExpansion_IsZeroOnePolytope
import Definitions.Def_ZeroOneExpansion_polyDim
import Definitions.Def_ZeroOneExpansion_edgeExpansion

set_option autoImplicit false

namespace ZeroOneExpansion

/-- **Theorem 1** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.1). There exist a constant `c > 0` and an infinite sequence of
full-dimensional 0/1-polytopes `(Pn)_{n≥1}` with dimensions tending to infinity such that, for all
sufficiently large `n`, `h(G(Pn)) ≤ exp(−c dim(Pn))`. In particular, `h(G(Pn)) < 1` for all
sufficiently large `n`.

**Formalization Note** The sequence is indexed by `ℕ`; the polytope `P n` lives in `ℝ^{d n}` and is
required to be a 0/1-polytope and full-dimensional (`Grunbaum2003.IsDPolytope`: a finite nonempty
hull with affine span the whole space) for every `n ≥ 1`. `G(P)` is `Grunbaum2003.polytopeGraph`,
`h` is `edgeExpansion` (`EReal`-valued, `⊤` when no set is admissible, so the bounds are not
vacuous), and `dim` is `polyDim`. The constant `c` is chosen before the sequence and before "for all
sufficiently large `n`". -/
theorem theorem_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ (d : ℕ → ℕ) (P : (n : ℕ) → Set (Fin (d n) → ℝ)),
      (∀ n, 1 ≤ n → IsZeroOnePolytope (P n) ∧ Grunbaum2003.IsDPolytope (P n)) ∧
      Filter.Tendsto (fun n => polyDim (P n)) Filter.atTop Filter.atTop ∧
      (∀ᶠ n in Filter.atTop, edgeExpansion (Grunbaum2003.polytopeGraph (P n)) ≤
        ((Real.exp (-c * (polyDim (P n) : ℝ)) : ℝ) : EReal)) ∧
      (∀ᶠ n in Filter.atTop, edgeExpansion (Grunbaum2003.polytopeGraph (P n)) < 1) := by sorry

end ZeroOneExpansion
