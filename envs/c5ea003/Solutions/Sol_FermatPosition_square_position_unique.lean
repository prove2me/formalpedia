-- Prove2me | solution 1 for FermatPosition.square_position_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:39:56.583777+00:00
-- url     : https://prove2.me/submissions/baf609bf-dfcf-4f5e-ad4c-d66078935f8b

-- Sol generated from NumberTheory/FermatPositionTerminal.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionGeometry
import Theorems.Thm_FermatPosition_semiprime_factor_pairs
/-
# Square positions of the sieve polynomial: the terminal Fermat position

Third companion to `Catalog/NumberTheory/FermatPositionGeometry.lean`.

Among all positions `j` of the sieve polynomial `v(j) = (b + j)^2 - N` the *square*
positions — those with `v(j)` a perfect square — are exactly the factorizations of `N`.
This is Fermat's method, and it gives the one piece of **exactly known** positional
geometry of the smooth locus, against which any statistical claim about hit positions can
be calibrated.

Main results.

* `sieveVal_eq_sq_iff` : `v(j) = k²` iff `N = (b + j - k)(b + j + k)`.
* `sieveVal_at_mid` : writing `N = s² - d²`, the position `s - b` is a square position
  with value `d²`; for `N = p q` with `p + q = 2s`, `q - p = 2d` this is the *terminal
  Fermat position*.
* `terminal_position_bound` : `2 b (s - b) ≤ d²`, i.e. the terminal position obeys the
  same linear magnitude law `2 b j ≤ v(j)` as every other position.  Balanced semiprimes
  (small `d` relative to `√N`) have their terminal position at small `j`; this is a
  *magnitude* statement, not extra positional structure.
* `semiprime_factor_pairs` : the factorizations of a semiprime.
* `square_position_unique` : the only square positions of a semiprime sieve are the
  trivial one (`b + j - k = 1`) and the terminal Fermat position `2 (b + j) = p + q`.
-/

open FermatPosition

/-- A position is a *square position* exactly when it exhibits a factorization of `N`. -/
theorem sieveVal_eq_sq_iff (b N j k : ℤ) :
    sieveVal b N j = k ^ 2 ↔ N = (b + j - k) * (b + j + k) := by
  simp only [sieveVal]
  constructor <;> intro h <;> nlinarith [h]







open FermatPosition in
theorem solution{b j k : ℤ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≤ q) (hk : 0 ≤ k) (hu : 1 < b + j - k)
    (hval : sieveVal b ((p : ℤ) * q) j = k ^ 2) :
    2 * (b + j) = (p : ℤ) + q := by
  have hfac : ((p : ℤ) * q) = (b + j - k) * (b + j + k) := (sieveVal_eq_sq_iff _ _ _ _).1 hval
  set u : ℤ := b + j - k with hudef
  set w : ℤ := b + j + k with hwdef
  have huw : u ≤ w := by simp only [hudef, hwdef]; linarith
  have hu0 : 0 < u := by omega
  have hw0 : 0 < w := lt_of_lt_of_le hu0 huw
  have hnat : u.toNat * w.toNat = p * q := by
    have : ((u.toNat * w.toNat : ℕ) : ℤ) = ((p * q : ℕ) : ℤ) := by
      push_cast [Int.toNat_of_nonneg (le_of_lt hu0), Int.toNat_of_nonneg (le_of_lt hw0)]
      linarith [hfac]
    exact_mod_cast this
  have hle : u.toNat ≤ w.toNat := by omega
  rcases semiprime_factor_pairs hp hq hpq hnat hle with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exfalso
    have : u = 1 := by omega
    omega
  · have hu' : u = (p : ℤ) := by omega
    have hw' : w = (q : ℤ) := by omega
    simp only [hudef, hwdef] at hu' hw'
    linarith
