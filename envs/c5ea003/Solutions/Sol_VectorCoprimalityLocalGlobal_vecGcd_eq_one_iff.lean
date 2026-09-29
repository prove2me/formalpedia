-- Prove2me | solution 1 for VectorCoprimalityLocalGlobal.vecGcd_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:52:17.443957+00:00
-- url     : https://prove2.me/submissions/9c71f7b6-5691-4cc5-bc52-ba966217b388

-- Sol generated from Bridges/PosetTheory/VectorCoprimalityLocalGlobal.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_VectorCoprimalityLocalGlobal

/-!
# Local-Global Bridge for Integer Vector Coprimality

This file formalizes the statement that **coprimality of an integer vector is a local
(per-prime) condition**, the foundational fact behind the Euler-product factorization of the
autocorrelation of simultaneously visible lattice points.

## Main definitions

* `VectorCoprimalityLocalGlobal.vecGcd w` : the (non-negative) gcd of all coordinates of an
  integer vector `w : Fin k → ℤ`.
* `VectorCoprimalityLocalGlobal.redMod p w` : the coordinatewise reduction of `w` modulo `p`.
* `VectorCoprimalityLocalGlobal.IsPrim x` : the coordinates of `x : Fin k → R` generate the unit
  ideal of the commutative ring `R` (a representation-independent primitivity condition).
* `VectorCoprimalityLocalGlobal.primDensity n k` : the density of primitive residue vectors in
  `(ZMod n) ^ k`.

## Main results

* `dvd_vecGcd_iff` (Theorem 1): `d ∣ vecGcd w ↔ ∀ i, d ∣ w i`.
* `redMod_eq_iff` (Theorem 2): `redMod p v = redMod p x ↔ (p : ℤ) ∣ vecGcd (v - x)`.
* `vecGcd_eq_one_iff` (Theorem 3, **the local-global bridge**):
  `vecGcd w = 1 ↔ ∀ p : ℕ, p.Prime → redMod p w ≠ 0`.
* `primDensity_mul` (corrected Theorem 4): for coprime `p q`,
  `primDensity (p*q) k = primDensity p k * primDensity q k`.

## Note on Theorem 4 of the research brief

The research brief proposed a "Theorem 4" of the form
`localDensity (p*q) S = localDensity p S * localDensity q S`, where
`localDensity p S = 1 - |redMod p '' S| / p^k`.  **This statement is false**: see
`localDensity_mul_counterexample` below, which exhibits `p = 2`, `q = 3`, `k = 1` and a two-point
set `S` for which the image cardinalities are all `2`, giving
`localDensity 6 S = 2/3 ≠ 0 = localDensity 2 S * localDensity 3 S`.
The image of a *fixed* finite set of integer vectors under reduction is not a CRT "product/cylinder"
set, so its cardinality is not multiplicative.

The multiplicativity that genuinely underlies the Euler product is the multiplicativity of the
**density of primitive residue vectors** (a Jordan-totient style quantity), captured here by
`primDensity_mul`.  The brief's definitions `redModFinset` and `localDensity` are retained (with the
counterexample proven) so that the record is complete.
-/

open Finset

open VectorCoprimalityLocalGlobal

/-! ## Definitions -/



/-! ## Basic properties of `vecGcd` -/


theorem vecGcd_nonneg {k : ℕ} (w : Fin k → ℤ) : 0 ≤ vecGcd w := by
  rw [vecGcd, ← Finset.normalize_gcd, ← Int.abs_eq_normalize]; exact abs_nonneg _

/-! ## Theorem 1 -/

/-- **Theorem 1.** An integer `d` divides the gcd of the coordinates of `w` iff it divides every
coordinate. -/
theorem dvd_vecGcd_iff {k : ℕ} (d : ℤ) (w : Fin k → ℤ) :
    d ∣ vecGcd w ↔ ∀ i, d ∣ w i := by
  rw [vecGcd, Finset.dvd_gcd_iff]; simp

/-! ## Theorem 2 -/

/-- **Theorem 2.** Two integer vectors reduce to the same class modulo `p` iff `p` divides the gcd
of their coordinatewise difference. -/
theorem redMod_eq_iff {k : ℕ} (p : ℕ) (v x : Fin k → ℤ) :
    redMod p v = redMod p x ↔ (p : ℤ) ∣ vecGcd (v - x) := by
  rw [funext_iff, dvd_vecGcd_iff]
  refine forall_congr' (fun i => ?_)
  simp only [redMod, Pi.sub_apply]
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
  exact dvd_sub_comm

theorem redMod_zero {k : ℕ} (p : ℕ) : redMod p (0 : Fin k → ℤ) = 0 := by
  funext i; simp [redMod]

/-- The reduction of `w` modulo `p` is the zero vector iff `p` divides the gcd of its
coordinates. -/
theorem redMod_eq_zero_iff {k : ℕ} (p : ℕ) (w : Fin k → ℤ) :
    redMod p w = 0 ↔ (p : ℤ) ∣ vecGcd w := by
  have h := redMod_eq_iff p w 0
  rw [sub_zero, redMod_zero] at h
  exact h

/-! ## Theorem 3 — the local-global bridge -/


/-! ## Theorem 4

The brief's proposed multiplicativity `localDensity (p*q) S = localDensity p S * localDensity q S`
is false.  We record the brief's definitions and disprove the claim, then state and prove the
correct multiplicative density. -/






/-! ### Corrected Theorem 4: multiplicativity of the primitive-residue density -/








open VectorCoprimalityLocalGlobal in
theorem solution{k : ℕ} (w : Fin k → ℤ) :
    vecGcd w = 1 ↔ ∀ p : ℕ, p.Prime → redMod p w ≠ 0 := by
  simp only [ne_eq, redMod_eq_zero_iff]
  constructor
  · intro h p hp hdvd
    rw [h] at hdvd
    have hle := Int.le_of_dvd (by norm_num) hdvd
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    omega
  · intro h
    have hnn := vecGcd_nonneg w
    by_contra hne
    have hna : (vecGcd w).natAbs ≠ 1 := by
      intro hcontra
      apply hne
      have := Int.natAbs_of_nonneg hnn
      omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hna
    apply h p hp
    have : (p : ℤ) ∣ ((vecGcd w).natAbs : ℤ) := Int.natCast_dvd_natCast.mpr hpd
    rwa [Int.natAbs_of_nonneg hnn] at this
