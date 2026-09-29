-- Prove2me | solution 1 for BerggrenRationalStars.star_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:46:54.706986+00:00
-- url     : https://prove2.me/submissions/0f124773-e8b2-4413-996a-be4772742eaa

-- Sol generated from Cryptography/BerggrenStars/RationalStars.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_RationalStars
import Theorems.Thm_BerggrenRationalStars_charge_odd_of_odd_odd
import Theorems.Thm_BerggrenRationalStars_exists_seed_of_charge

/-!
# The rational stars of the Berggren tree: the exact charge spectrum and the visibility law

`Cryptography.BerggrenStars.HypercycleStars` shows that over *every* rational boundary point
`p/q` of the Poincaré half-plane sits a pencil ("star") of Euclidean rays, the hypercycles at
distance `arsinh (|k|/q)` from the geodesic over `p/q`, indexed by the **star charge**

  `k = q * n - p * m`   of the Berggren node `z(m,n) = (n + i)/m`.

That file leaves open the arithmetic question that actually governs the *picture*: **which
charges `k` occur?** The answer, proved here, is a clean parity law, and it explains exactly
which rational points show a visible star.

## Main results

* `charge_odd_of_odd_odd` : if `p` and `q` are **both odd** then every Berggren node has an
  **odd** charge at `p/q`. Half of the pencil is empty.
* `exists_seed_of_charge` : conversely, for `0 < p < q` coprime, **every** nonzero integer `k`
  allowed by that parity law is the charge of infinitely many nodes. The proof is an explicit
  `SL₂(ℤ)` construction: with `q x - p y = 1` and `A = 1 + k(x+y) + 2k²j`, the pair
  `(m,n) = (qA + yk, pA + xk)` is a Euclid seed of charge `k`, because
  `gcd(m,n) = gcd(A,k) = 1` (`isCoprime_of_sl2_charge`).
* `charge_zero_iff` : the *central* ray `k = 0` (the geodesic itself) carries a node iff
  `(q,p)` is itself a seed, i.e. iff `p + q` is odd.
* `star_spectrum` : the two results combined — the realised charge set at `p/q` is exactly
  `ℤ \ {0}` intersected with the allowed parity class (plus `0` when `p+q` is odd).
* `starGapNum`, `charge_gap`, `star_gap_attained` : the **resolution law**. Two nodes lying on
  different rays of the star at `p/q` have `sinh`-distances to the central geodesic differing
  by at least `δ(p/q) = (1 or 2)/q`, and this is attained. So the star at `p/q` is a pencil
  whose angular resolution is `δ(p/q)`: the smaller `q`, and the *worse* the parity of `p+q`,
  the more visible the star.
* `visible_rationals` : the finite classification. The rationals of `[0,1]` with
  `δ ≥ 2/5` are exactly `0, 1/5, 1/3, 1/2, 3/5, 1` — precisely the boundary points at which
  radial lines are seen in a rendered star map (`0`, `0.2`, `0.33`, `0.5`, `1`), together with
  the falsifiable prediction `0.6`. Note `1/4 = 0.25` is excluded although `4 < 5`: even
  denominators are penalised by the parity law.

All statements about distances are for Mathlib's genuine hyperbolic metric on
`UpperHalfPlane`, via `BerggrenHypercycleStars.distVLine`.
-/

open BerggrenRationalStars

open BerggrenHypercycleStars

/-! ## Part 0. The star charge -/



/-! ## Part 1. Quantisation: the parity obstruction -/



/-! ## Part 2. Realisation: the `SL₂(ℤ)` ray construction -/




/-! ## Part 3. The exact charge spectrum of a rational star -/



/-! ## Part 4. The resolution law and the visible rationals -/







open BerggrenRationalStars in
theorem solution(p q : ℕ) (hp : 0 < p) (hlt : p < q) (hcop : Nat.Coprime p q) (k : ℤ) :
    (∃ m n : ℕ, IsSeed m n ∧ starCharge p q m n = k) ↔ ((p + q) % 2 = 1 ∨ Odd k) := by
  constructor
  · rintro ⟨m, n, hseed, rfl⟩
    rcases Nat.even_or_odd (p + q) with he | ho
    · right
      have hp2 : p % 2 = 1 := by
        rcases Nat.even_or_odd p with hpe | hpo
        · exfalso
          have hq2 : q % 2 = 0 := by
            rw [Nat.even_iff] at he hpe; omega
          have hp2 : p % 2 = 0 := by rw [Nat.even_iff] at hpe; omega
          have : 2 ∣ Nat.gcd p q := Nat.dvd_gcd (by omega) (by omega)
          rw [hcop] at this
          omega
        · rw [Nat.odd_iff] at hpo; exact hpo
      have hq2 : q % 2 = 1 := by rw [Nat.even_iff] at he; omega
      exact charge_odd_of_odd_odd hp2 hq2 hseed
    · left; rw [Nat.odd_iff] at ho; exact ho
  · intro hk
    by_cases hk0 : k = 0
    · subst hk0
      have hpar : (p + q) % 2 = 1 := by
        rcases hk with h | h
        · exact h
        · exact absurd h (by simp)
      refine ⟨q, p, ⟨hp, hlt, Nat.coprime_comm.mp hcop, by omega⟩, ?_⟩
      simp [starCharge]
      ring
    · obtain ⟨m, n, hs, _, hc⟩ := exists_seed_of_charge p q hp hlt hcop k hk0 hk 0
      exact ⟨m, n, hs, hc⟩
