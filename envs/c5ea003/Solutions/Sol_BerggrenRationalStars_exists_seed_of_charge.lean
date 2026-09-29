-- Prove2me | solution 1 for BerggrenRationalStars.exists_seed_of_charge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:44:51.372594+00:00
-- url     : https://prove2.me/submissions/33171e30-c1fb-4cf5-ac25-fe1c319547e5

-- Sol generated from Cryptography/BerggrenStars/RationalStars.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_RationalStars

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

/-- Parity as a statement in `ZMod 2`. -/
theorem odd_iff_cast_zmod_two (z : ℤ) : Odd z ↔ ((z : ZMod 2) = 1) := by
  rw [Int.odd_iff, show ((1 : ZMod 2)) = ((1 : ℤ) : ZMod 2) by norm_num,
    ZMod.intCast_eq_intCast_iff']
  norm_num


/-! ## Part 2. Realisation: the `SL₂(ℤ)` ray construction -/

/-- The determinant-one change of variables. If `q x - p y = 1` then the map
`(A,k) ↦ (qA + yk, pA + xk)` is in `SL₂(ℤ)`, so it preserves coprimality: the node built from
`(A,k)` is primitive as soon as `A` and `k` are. -/
theorem isCoprime_of_sl2_charge {p q x y A k : ℤ} (hdet : q * x - p * y = 1)
    (h : IsCoprime A k) : IsCoprime (q * A + y * k) (p * A + x * k) := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨u * x - v * p, v * q - u * y, ?_⟩
  have hA : x * (q * A + y * k) - y * (p * A + x * k) = A * (q * x - p * y) := by ring
  have hk : q * (p * A + x * k) - p * (q * A + y * k) = k * (q * x - p * y) := by ring
  rw [hdet, mul_one] at hA hk
  calc (u * x - v * p) * (q * A + y * k) + (v * q - u * y) * (p * A + x * k)
      = u * (x * (q * A + y * k) - y * (p * A + x * k))
        + v * (q * (p * A + x * k) - p * (q * A + y * k)) := by ring
    _ = u * A + v * k := by rw [hA, hk]
    _ = 1 := huv

/-- The parity bookkeeping of the construction, as an identity in `ZMod 2`. -/
theorem parity_zmod_two (P Q X Y K A : ZMod 2) (hdet : Q * X - P * Y = 1)
    (hA : A = 1 + K * (X + Y)) (hpar : P + Q = 1 ∨ K = 1) :
    (P + Q) * A + (X + Y) * K = 1 := by
  revert hdet hA hpar
  revert P Q X Y K A
  decide


/-! ## Part 3. The exact charge spectrum of a rational star -/



/-! ## Part 4. The resolution law and the visible rationals -/







open BerggrenRationalStars in
theorem solution(p q : ℕ) (hp : 0 < p) (hlt : p < q) (hcop : Nat.Coprime p q)
    (k : ℤ) (hk : k ≠ 0) (hpar : (p + q) % 2 = 1 ∨ Odd k) (B : ℕ) :
    ∃ m n : ℕ, IsSeed m n ∧ B < m ∧ starCharge p q m n = k := by
  -- Bezout data `q x - p y = 1`
  obtain ⟨x, y, hdet⟩ : ∃ x y : ℤ, (q : ℤ) * x - (p : ℤ) * y = 1 := by
    have : IsCoprime (q : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd_natCast_natCast, Nat.Coprime] using (Nat.coprime_comm.mp hcop)
    obtain ⟨a, b, hab⟩ := this
    exact ⟨a, -b, by linarith [hab]⟩
  -- the free parameter, chosen ≡ 1 (mod k), even-shifted, and large
  set T : ℤ := x + y with hT
  set A₀ : ℤ := 1 + k * T with hA₀
  set C : ℤ := |A₀| + |x * k| + |y * k| + (B : ℤ) + 1 with hC
  have hCpos : 0 ≤ C := by positivity
  set j : ℤ := C with hj
  set A : ℤ := A₀ + 2 * k ^ 2 * j with hA
  have hk2 : (1 : ℤ) ≤ k ^ 2 := by
    rcases lt_trichotomy k 0 with h | h | h
    · nlinarith
    · exact absurd h hk
    · nlinarith
  have hAbig : C + 1 ≤ A := by
    have h1 : 2 * C ≤ 2 * k ^ 2 * j := by
      rw [hj]; nlinarith
    have h2 : -|A₀| ≤ A₀ := neg_abs_le A₀
    have h3 : |A₀| + 1 ≤ C := by
      have : (0 : ℤ) ≤ |x * k| + |y * k| + (B : ℤ) := by positivity
      omega
    omega
  -- the node
  set M : ℤ := (q : ℤ) * A + y * k with hM
  set N : ℤ := (p : ℤ) * A + x * k with hN
  have hApos : (0 : ℤ) < A := by omega
  have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hqp : (1 : ℤ) ≤ (q : ℤ) - (p : ℤ) := by
    have : (p : ℤ) < (q : ℤ) := by exact_mod_cast hlt
    omega
  have hxk : -|x * k| ≤ x * k := neg_abs_le _
  have hyk : -|y * k| ≤ y * k := neg_abs_le _
  have hNpos : 0 < N := by
    have : A ≤ (p : ℤ) * A := le_mul_of_one_le_left hApos.le hp1
    have hCx : |x * k| + 1 ≤ C := by
      have : (0 : ℤ) ≤ |A₀| + |y * k| + (B : ℤ) := by positivity
      omega
    omega
  have hMN : N < M := by
    have hdiff : M - N = ((q : ℤ) - p) * A + (y - x) * k := by rw [hM, hN]; ring
    have : A ≤ ((q : ℤ) - p) * A := le_mul_of_one_le_left hApos.le hqp
    have hCxy : |x * k| + |y * k| + 1 ≤ C := by
      have : (0 : ℤ) ≤ |A₀| + (B : ℤ) := by positivity
      omega
    have hexp : (y - x) * k = y * k - x * k := by ring
    have hxk' : x * k ≤ |x * k| := le_abs_self _
    omega
  have hMB : (B : ℤ) < M := by
    have hq1 : (1 : ℤ) ≤ (q : ℤ) := by omega
    have : A ≤ (q : ℤ) * A := le_mul_of_one_le_left hApos.le hq1
    have hCy : |y * k| + (B : ℤ) + 1 ≤ C := by
      have : (0 : ℤ) ≤ |A₀| + |x * k| := by positivity
      omega
    omega
  -- coprimality
  have hcopAk : IsCoprime A k := by
    refine ⟨1, -(T + 2 * k * j), ?_⟩
    rw [hA, hA₀]; ring
  have hcopMN : IsCoprime M N := isCoprime_of_sl2_charge hdet hcopAk
  -- back to naturals
  have hMpos : 0 < M := lt_trans hNpos hMN
  refine ⟨M.toNat, N.toNat, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · omega
  · omega
  · have hgcd : Int.gcd M N = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcopMN
    have h1 : M.natAbs = M.toNat := Int.natAbs_of_nonneg hMpos.le ▸ by omega
    have h2 : N.natAbs = N.toNat := Int.natAbs_of_nonneg hNpos.le ▸ by omega
    unfold Nat.Coprime
    rw [← h1, ← h2]
    exact hgcd
  · -- parity
    have hsum : (M.toNat : ℤ) + (N.toNat : ℤ) = ((p : ℤ) + q) * A + (x + y) * k := by
      rw [show (M.toNat : ℤ) = M by omega, show (N.toNat : ℤ) = N by omega, hM, hN]; ring
    have hodd : Odd ((M.toNat : ℤ) + N.toNat) := by
      rw [odd_iff_cast_zmod_two, hsum]
      have hAeq : ((A : ℤ) : ZMod 2) = 1 + ((k : ℤ) : ZMod 2) * (((x : ℤ) : ZMod 2)
          + ((y : ℤ) : ZMod 2)) := by
        have : A = 1 + k * (x + y) + 2 * (k ^ 2 * j) := by rw [hA, hA₀, hT]; ring
        rw [this]
        push_cast
        rw [show (2 : ZMod 2) = 0 from rfl]
        ring
      have hdet2 : ((q : ℤ) : ZMod 2) * ((x : ℤ) : ZMod 2) - ((p : ℤ) : ZMod 2)
          * ((y : ℤ) : ZMod 2) = 1 := by
        have := congrArg (fun z : ℤ => ((z : ZMod 2))) hdet
        push_cast at this
        simpa using this
      have hparity2 : ((p : ℤ) : ZMod 2) + ((q : ℤ) : ZMod 2) = 1 ∨ ((k : ℤ) : ZMod 2) = 1 := by
        rcases hpar with h | h
        · left
          have : Odd ((p : ℤ) + q) := by rw [Int.odd_iff]; omega
          rw [odd_iff_cast_zmod_two] at this
          push_cast at this
          exact this
        · right; exact (odd_iff_cast_zmod_two k).mp h
      have := parity_zmod_two ((p : ℤ) : ZMod 2) ((q : ℤ) : ZMod 2) ((x : ℤ) : ZMod 2)
        ((y : ℤ) : ZMod 2) ((k : ℤ) : ZMod 2) ((A : ℤ) : ZMod 2) hdet2 hAeq hparity2
      push_cast
      push_cast at this
      linear_combination this
    rw [Int.odd_iff] at hodd
    omega
  · omega
  · rw [starCharge, show (M.toNat : ℤ) = M by omega, show (N.toNat : ℤ) = N by omega, hM, hN]
    linear_combination k * hdet
