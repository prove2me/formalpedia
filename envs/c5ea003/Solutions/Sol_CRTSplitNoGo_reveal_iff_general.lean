-- Prove2me | solution 1 for CRTSplitNoGo.reveal_iff_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:54:01.741842+00:00
-- url     : https://prove2.me/submissions/8103bd92-14ab-4798-84ae-e9b2159f2814

-- Sol generated from Bridges/CRTSplitNoGoGeneral.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Definitions.Def_Bridges_CRTSplitNoGoClosureTime

/-!
# The CRT-Split No-Go, Part V: general moduli, barrier 5, and the boundary of the no-go

Three complements to Parts I–IV.

* **General moduli.**  Fact 1 is not special to semiprimes: for any `N > 1`, an integer `d`
  reveals a nontrivial factor of `N` iff some prime factor of `N` divides `d` while `N` itself
  does not (`reveal_iff_general`).  Reveal = *partial* agreement across the CRT decomposition.

* **Barrier 5 (structurally simple maps reveal nothing at all).**  A map that forgets its
  input — a constant polynomial, the paradigmatic "`N`-only" iteration — never reveals a
  factor, at any pair of times `1 ≤ s < t` (`constant_map_no_reveal`).  More generally any map
  whose two reduced orbits close *simultaneously* is blind (`no_reveal_of_simultaneous`).

* **The boundary (adversarial review).**  The no-go is a statement about *regimes*, not a
  universal lower bound: there are `N` for which an `N`-independent iteration reveals a factor
  at an exponent that is reached in `O(log M)` multiplications.  We verify this on the CTST
  modulus itself: `ord_631(2) = 45` divides `45` while `ord_541(2) = 540` does not, so
  `gcd(2^45 - 1, 341371) = 631` (`pollard_pm1_fast_demo`).  Both `630 = 2·3²·5·7` and
  `540 = 2²·3³·5` are smooth, which is exactly regime (b): the cost is the smoothness of the
  orders, an invariant of `p` and `q` that is invisible in `N` — so no *algorithm* can decide
  in advance which regime it is in.  A universal `poly(log N)` lower bound valid for *all*
  `N`-explicit maps would be equivalent to the hardness of factoring and is not claimed here.
-/

open CRTSplitNoGo

open Polynomial

/-! ## Fact 1 for an arbitrary modulus -/


/-! ## Barrier 5: structurally simple maps -/




/-! ## The boundary of the no-go: a fast reveal in regime (b) -/





open CRTSplitNoGo in
theorem solution{N : ℕ} (hN : 1 < N) (d : ℤ) :
    RevealsFactor N d ↔ (∃ r : ℕ, r.Prime ∧ r ∣ N ∧ (r : ℤ) ∣ d) ∧ ¬ ((N : ℤ) ∣ d) := by
  set g : ℕ := Int.gcd d (N : ℤ) with hg
  have hgN : g ∣ N := Int.ofNat_dvd.mp (by simpa using Int.gcd_dvd_right d (N : ℤ))
  have hgd : (g : ℤ) ∣ d := Int.gcd_dvd_left d (N : ℤ)
  have hgle : g ≤ N := Nat.le_of_dvd (by omega) hgN
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd (by omega : g ≠ 1)
      exact ⟨r, hr, hrg.trans hgN, (Int.natCast_dvd_natCast.mpr hrg).trans hgd⟩
    · intro hNd
      have : N ∣ g := Int.dvd_gcd hNd dvd_rfl
      have := Nat.le_of_dvd (by omega) this
      omega
  · rintro ⟨⟨r, hr, hrN, hrd⟩, hNd⟩
    have hrg : r ∣ g := Int.dvd_gcd hrd (Int.natCast_dvd_natCast.mpr hrN)
    have hgpos : 0 < g := by
      rcases Nat.eq_zero_or_pos g with h0 | h0
      · rw [h0] at hgN; exact absurd (Nat.eq_zero_of_zero_dvd hgN) (by omega)
      · exact h0
    refine ⟨lt_of_lt_of_le hr.one_lt (Nat.le_of_dvd hgpos hrg), ?_⟩
    rcases lt_or_eq_of_le hgle with h | h
    · exact h
    · exact absurd (h ▸ hgd) hNd
