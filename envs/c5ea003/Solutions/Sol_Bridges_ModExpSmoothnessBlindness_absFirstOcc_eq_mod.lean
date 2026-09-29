-- Prove2me | solution 1 for Bridges.ModExpSmoothnessBlindness.absFirstOcc_eq_mod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:10:56.609057+00:00
-- url     : https://prove2.me/submissions/43081b9e-038f-4b6a-9a2e-220233046b96

-- Sol generated from Bridges/ModExpSmoothnessBlindness.lean
import Mathlib
import Definitions.Def_Bridges_ModExpSmoothnessBlindness
/-
# Mod-exponential windows are smoothness-blind

A *Bridges* file connecting three normally separate areas:

* **finite group theory** (multiplicative order in `(ZMod N)ˣ`),
* **combinatorics of words** (the collision pattern of a finite window of a sequence),
* **statistical learning** (the rank statistic `AUC` of a scoring rule).

## Scientific context

Experiment 397 of the factoring research loop (SEQSMOOTH-NULL) asked whether the
`p−1` smoothness class of a semiprime `N = p·q` leaks into the *statistics of a short
window* `s_x = a^x mod N`, `x < m`, with `m` far smaller than the smoothness bound `B`.
Empirically the answer was a hard null: 42 windowed features gave a permutation
`p = 0.502` and a 5-fold logistic `AUC = 0.500`, while Pollard's `p−1` method with
`B = 100` factored 35/36 of the SMOOTH instances and 0/36 of the GENERAL instances.

This file turns the empirical null into theorems.  The three pillars are:

1. **Structure theorem** (`firstOcc_eq_mod`, `distinctCount_eq`).  The entire
   *collision structure* of the window — which indices carry equal values — is the
   function `x ↦ x % d` where `d = ord_N(a)`.  Nothing else about `N` survives:
   in particular no arithmetic information about the factorisation of `p − 1`.

2. **Blindness / information bound** (`windowPattern_blind`, `collisionFeature_blind`,
   `windowPatterns_ncard_le`).  Any statistic that reads only the collision structure
   of a length-`m` window takes at most `m + 1` distinct values over *all* moduli and
   bases, and agrees on any two instances with `min m d` equal.  Composed with the
   `AUC` bridge (`auc_eq_half_of_blind`) this yields `AUC = 1/2` *exactly* — the
   experiment's 0.500 is not a sampling artefact but a theorem.

3. **The weakness is real, and only the `p−1` method sees it**
   (`pMinusOne_succeeds`, `pMinusOne_fails`) instantiated on an explicit matched pair

   * `N₁ = 1009 · 1019` (SMOOTH: `1008 = 2^4·3^2·7` divides `M = lcm(1..20)`),
   * `N₂ = 1019 · 1039` (GENERAL: `509 ∤ M`, `173 ∤ M`),

   for which `gcd(2^M − 1, N₁)` is a *proper nontrivial* divisor while
   `gcd(2^M − 1, N₂) = 1`, yet the two length-256 windows of `2^x` have *identical*
   collision structure, hence identical value under every collision feature, hence
   `AUC = 1/2`.

## Honest scope

The blindness theorems of §2–§13 cover the *collision-structure* features (distinct
count, self-collision gap, repeat/run pattern, any function of the pattern word).
Section 14 adds the first value-level result: over a *full period* the set of values is
invariant under the base action `a ↦ a^t`, `gcd(t, ord_N a) = 1`
(`periodValues_base_invariant`), so every symmetric value feature depends on the cyclic
subgroup alone.  Value-level features of a *short* window (top-bit balance of the first
`m ≪ d` terms) remain outside the scope of these theorems; the experiment found them
null too, but that is an empirical statement, not one proved here.

Sections 15–16 remove the last piece of ad-hockery from the blindness statements:
§15 abstracts the order lower bound into a *decidable certificate*
(`le_orderOf_of_certificate`, `le_orderOf_zmod_of_certificate`), and §16 uses it, with
the elementary bound `p < 2^(ord_p 2)` (`lt_two_pow_orderOf_two`), to build an infinite
blind family for **every** window length `m` (`exists_infinite_blind_family`), so that
`AUC = 1/2` holds for every real statistic at every length
(`no_free_lunch_auc_all_lengths`), not merely at the `m = 256` of the experiment.
-/

open Bridges.ModExpSmoothnessBlindness

open Finset

/-! ## 1. The mod-exponential window and its order -/






/-! ## 2. The pattern word of a window -/








/-! ## 3. Information bound: a length-`m` window carries at most `log₂(m+1)` bits -/



/-! ## 4. The distinct-count feature -/




/-! ## 5. The learning bridge: a blind feature has `AUC = 1/2` -/



/-! ## 6. Pollard's `p−1`: the weakness is real -/




/-! ## 7. Auxiliary order arithmetic -/





/-! ## 8. The explicit matched pair: SMOOTH vs GENERAL

`bigM = lcm(1,…,20) = 232792560 = 2^4·3^2·5·7·11·13·17·19` is the exponent used by
Pollard's `p−1` method with bound `B = 20`.

* `N_smooth  = 1009 · 1019`, and `1009 − 1 = 1008 = 2^4·3^2·7` divides `bigM`;
* `N_general = 1019 · 1039`, and `1019 − 1 = 2·509`, `1039 − 1 = 2·3·173`, whose large
  prime factors `509`, `173` exceed the bound.

Both moduli share the prime `1019`, whose base-2 order is a multiple of `509 > 256`;
this is what pins the window statistics of the two classes to the *same* value.
-/














/-! ### 8a. The classes really differ: Pollard `p−1` separates them -/



/-! ### 8b. …yet the length-256 windows are literally indistinguishable -/







/-! ### 8c. The null result, packaged -/



/-! ## 9. Mechanism: CRT decomposition of the order

Why can the window not see smoothness?  Because the only invariant it sees is
`ord_N(a) = lcm (ord_p a) (ord_q a)`, and a *large* order is compatible with either
smoothness class: `ord_p a` divides `p − 1`, but its size says nothing about the
factorisation of `p − 1` into primes.  The theorem below is the exact CRT statement. -/


/-! ## 10. The exact criterion for the `p−1` method, and an infinite blind family -/










/-! ## 11. No free lunch: every collision feature scores chance on the family -/





/-! ## 12. Pigeonhole form of the information bound (barrier 4)

The counting bound of §3 has a sharp combinatorial consequence: among any `m + 2`
odd moduli, two already have *identical* length-`m` windows up to collision structure.
So a window of length `m` cannot even name one modulus out of `m + 2`, let alone
separate a smoothness class. -/




/-! ## 13. The null is a fact about cyclic prefixes, not about factoring

Nothing in §2 used the modulus: only that the element has finite order.  The blindness
phenomenon is therefore a structural theorem about prefixes of cyclic orbits in an
arbitrary monoid — mod-exponential sequences, elliptic-curve multiples and
function-field analogues all inherit it. -/






/-! ## 14. Value-level blindness over a full period

§2–§12 cover *collision-structure* features.  This section takes the first step beyond
them, to the **values** themselves.  The base of a mod-exponential sequence is a free
parameter: replacing `a` by `a^t` with `t` coprime to `d = ord_N(a)` is a bijection of
the cyclic group `⟨a⟩` and reindexes the orbit.  We prove that the *set of values of a
full-period window is unchanged*, so every value-level feature that reads the window as
a set (top-bit balance, value histogram, extreme values, any symmetric statistic) is
blind to the exponent `t`: it depends on `(N, ⟨a⟩)` only, never on which generator of
the subgroup is used, hence never on the arithmetic of `t`.

Together with `mexpOrd_mul_coprime` this says the only channel left open at the value
level is the *subgroup itself*, whose size `lcm(ord_p a, ord_q a)` is smoothness-agnostic. -/









/-! ## 15. A decidable certificate for large multiplicative order

The blind families of §10 rest on one quantitative input: a *lower bound* for the
multiplicative order `ord_p(2)`.  Computing the order itself is infeasible, but a lower
bound never needs it — one non-vanishing power suffices.  The following is the abstract
form of the ad-hoc argument used for `p = 1019` in §8, and it is the general tool asked
for by Conjecture 4 of `FUTURE_DIRECTIONS.md`.

If `r` is a prime dividing an exponent `n` that annihilates `g`, and `g^(n/r) ≠ 1`, then
`r ∣ ord(g)`; in particular `r ≤ ord(g)`.  The hypothesis is a single equality test in
the ambient monoid, hence decidable in `ZMod p`. -/






/-! ## 16. Blind families of every window length

§10 exhibits one infinite blind family, rigid up to window length 256.  With the
certificate of §15 and the elementary bound `p < 2^(ord_p 2)` we can now produce, for
*every* `m`, an infinite family of moduli whose length-`m` windows are literally
identical — so the no-free-lunch statement of §11 holds at every window length, not just
at the one used in the experiment.  This is the constructive half of Conjecture 2. -/













open Bridges.ModExpSmoothnessBlindness in
open Classical in
theorem solution{M : Type*} [Monoid M] {g : M} (hg : IsOfFinOrder g) (n : ℕ) :
    absFirstOcc g n = n % orderOf g := by
  have hd : 0 < orderOf g := hg.orderOf_pos
  have hmem : g ^ (n % orderOf g) = g ^ n := hg.pow_eq_pow_iff_modEq.mpr (Nat.mod_modEq n _)
  unfold absFirstOcc
  apply le_antisymm
  · exact Nat.find_le hmem
  · rw [Nat.le_find_iff]
    intro y hy hcon
    have h3 : y % orderOf g = n % orderOf g := hg.pow_eq_pow_iff_modEq.mp hcon
    have hyd : y < orderOf g := lt_trans hy (Nat.mod_lt _ hd)
    rw [Nat.mod_eq_of_lt hyd] at h3
    omega
