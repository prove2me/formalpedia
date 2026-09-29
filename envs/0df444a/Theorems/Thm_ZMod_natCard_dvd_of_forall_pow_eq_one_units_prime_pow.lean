-- Prove2me | Theorems.Thm_ZMod_natCard_dvd_of_forall_pow_eq_one_units_prime_pow
-- name    : ZMod.natCard_dvd_of_forall_pow_eq_one_units_prime_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/2f1fd831-5ffc-50e2-bfcc-d445aef398a6
-- title:
--   Subgroup of (ℤ/p^{vₚ(q)+1})^× killed by q has order dividing q
-- statement:
--   Let $p$ be a natural number which is prime, let $q$ be a nonzero natural number, and put $N = v_p(q) + 1$, where $v_p$ denotes the $p$-adic valuation `padicValNat p q` of $q$. Let $H$ be a subgroup of the unit group $(\mathbf Z/p^{N}\mathbf Z)^\times$ of the ring `ZMod (p ^ (padicValNat p q + 1))`, and suppose that every element $x$ of $H$ satisfies $x^{q} = 1$ in that unit group. The conclusion is that the cardinality of $H$, taken as the natural number `Nat.card H`, divides $q$. Thus a $q$-torsion subgroup of the units modulo $p^{v_p(q)+1}$ has order dividing $q$; note that the exponent of the modulus is exactly one more than the $p$-adic valuation of $q$, which is what makes the assertion true, and that no hypothesis of oddness of $p$ is imposed.
--
--   The statement is the elementary finite-group count that bounds the order of the group of $q$-torsion units modulo a prime power just beyond the $p$-part of $q$; in particular it gives $\#\mu_q(\mathbf Z/p^{N}\mathbf Z) \mid q$. It is used in the flat-cohomology estimate [`AlgebraicGeometry.exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff`](thm.html#AlgebraicGeometry.exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff), where such a count controls the degree-zero cohomology of a cokernel sheaf attached to the multiplicative group scheme of $q$-th roots of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZMod_natCard_dvd_of_forall_pow_eq_one_units_prime_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ZMod.natCard_dvd_of_forall_pow_eq_one_units_prime_pow
    (p : ℕ) (hp : p.Prime) (q : ℕ) (hq : q ≠ 0)
    (H : Subgroup (ZMod (p ^ (padicValNat p q + 1)))ˣ) (hH : ∀ x ∈ H, x ^ q = 1) :
    Nat.card H ∣ q := by sorry
