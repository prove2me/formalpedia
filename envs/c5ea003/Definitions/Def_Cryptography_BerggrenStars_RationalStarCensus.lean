-- Prove2me | Definitions.Def_Cryptography_BerggrenStars_RationalStarCensus
-- name    : Cryptography_BerggrenStars_RationalStarCensus
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T17:02:04.552235+00:00
-- url     : https://prove2.me/theorems/940ad45a-f03c-4009-b7e7-0bcef5085eb1
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenStars_RationalStarCensus
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenStars.RationalStarCensus`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenStars/RationalStarCensus.lean by skeleton subtraction
import Mathlib

/-!
# The census of a rational star ray: a totient brightness law

How *bright* is a radial line? Along the ray of charge `k` at the boundary rational `p/q` the
Berggren nodes sit at some of the lattice points `(m + tq, n + tp)`; this file computes exactly
which ones, and counts them.

The tool is the `SL₂(ℤ)` change of variables of `RationalStars`: choosing Bezout data
`q x - p y = 1`, the integer points of the ray of charge `k` are exactly

  `(m, n) = (q A + y k,  p A + x k)`,  `A = x m - y n ∈ ℤ`,

and in the coordinates `(A, k)` the two arithmetic conditions defining a Berggren node become
transparent:

  * coprimality `gcd(m,n) = 1`  ⟺  `gcd(A,k) = 1`   (`isCoprime_ray_iff`);
  * parity `m + n` odd          ⟺  `(p+q)A + (x+y)k` odd  (`sum_eq_ray`).

## Main results

* `ray_param_eq` : the `SL₂(ℤ)` parametrisation of a ray.
* `isCoprime_ray_iff` : coprimality of a node ⟺ coprimality of its ray parameter with the
  charge. **The charge is the only arithmetic obstruction along a ray.**
* `parity_free_of_both_odd`, `parity_free_of_even_charge` : the two regimes in which the parity
  condition along the ray is automatic.
* `window_coprime_card` : `#{A ∈ [a, a+2k) : gcd(k,A) = 1} = 2 φ(k)`.
* `ray_census_both_odd`, `ray_census_even_charge`, `ray_census_mixed` : the **brightness law**,
  a clean trichotomy. A window of `2k` consecutive ray parameters carries

    - `2 φ(k)` nodes if `p, q` are both odd (any odd charge `k`),
    - `2 φ(k)` nodes if `p + q` is odd and the charge `k` is even,
    - `φ(k) = φ(2k)` nodes if `p + q` is odd and the charge `k` is odd — *half brightness*.

  Together with the resolution law of `RationalStars`, this is the quantitative description of
  the star map: the star at `p/q` has angular spacing `(1 or 2)/q` in `sinh`, and each of its
  rays has linear node density `φ(k)/k` or `φ(k)/(2k)`. The brightest rays are the ones of
  smallest charge, and `k = ±1` at a both-odd star gives density `1`.
-/

namespace BerggrenRationalStars

open Finset

/-! ## Part 1. The `SL₂(ℤ)` parametrisation of a ray -/

/-- The **ray parameter** of an integer point, relative to Bezout data `q x - p y = 1`. -/
def rayParam (x y m n : ℤ) : ℤ := x * m - y * n




/-! ## Part 2. The two parity-free regimes -/




/-! ## Part 3. The brightness law -/







/-! ## Part 4. The third regime: half-brightness at mixed parity

The remaining case is `p + q` odd with an **odd** charge `k`.  Here the parity condition is not
automatic: it pins the ray parameter `A` to a *single residue class mod 2*, and the brightness
drops by exactly a factor of two, from `2 φ(k)` to `φ(k) = φ(2k)` nodes per window of `2k`.
This is the arithmetic shadow of the resolution law: at a star `p/q` with `p+q` odd the rays are
spaced `1/q` apart in `sinh`, twice as finely as at a both-odd star, and correspondingly each
individual ray is only half as bright. -/





end BerggrenRationalStars


