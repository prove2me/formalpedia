-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_orbit_sampling_equivalence
-- name    : ZLIPPadding.Padding.Supplement.orbit_sampling_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:19:26.202482+00:00
-- url     : https://prove2.me/theorems/926a8a61-823a-4633-bde8-4544b3d8e473
-- title:
--   Theorem 3.3 — Two-way orbit-sampling equivalence
-- statement:
--   Fix a uniformly efficiently computable family $a(n)\in\mathbb Z^n\setminus\{0\}$ for $n\ge2$, whose squared norm $m=\|a(n)\|^2$ is bounded by one polynomial in $n$, and suppose $\kappa_{a(n)}\ne0$ in every such dimension. On promised rational input bases $B$ of lattices isometric to $\mathbb Z^n$, independent exact uniform sampling from the specified orbit and full ZLIP recovery admit both randomized polynomial-time oracle reductions. For every $0<\delta<1$,
--
--   $$\Pr[\text{recover an orthonormal basis of the whole lattice}]\ge1-\delta,$$
--
--   with time and samples polynomial in $n,m,\eta_a^{-1},\log(1/\delta),\ell$, where $\eta_a=|\kappa_a|/m^2$ and $\ell$ is the binary input length. The reverse reduction has exactly uniform output conditional on success, and success probability at least $1-\delta$. Both reductions are single finite oracle programs with polynomial witnesses fixed before all inputs and oracle rules. There is no polynomial orbit-cardinality premise. This companion theorem is independent of the padding goal.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time oracle equivalence → finite bit-stack programs, coordinate-output kernels, dyadic error budgets and uniform existential polynomial bounds; reason: binary execution makes the source complexity uniform; capped sampling preserves exact conditional uniformity
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 13 (PDF p. 14), Theorem 3.3

import Definitions.Def_ZLIPPadding_Padding_Supplement_Reductions

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem orbit_sampling_equivalence (a : (n : ℕ) → ZVec n)
    (ha : EfficientProfiles a)
    (hne : ∀ n, 2 ≤ n → a n ≠ 0)
    (hkap : ∀ n, 2 ≤ n → orbitKappa (a n) ≠ 0) :
    OrbitEquivalence a := by sorry

end ZLIPPadding.Padding.Supplement
