-- Prove2me | solution 1 for CRTSplitNoGo.crt_reveal_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:53:04.715712+00:00
-- url     : https://prove2.me/submissions/a77ab364-3547-4a60-a00b-c2ccafa94ead

-- Sol generated from Bridges/CRTSplitNoGo.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo

/-!
# The CRT-Split No-Go, Part I: the reveal mechanism

This file formalises the two structural facts underlying the claim that no classical
iteration built from `N` alone can factor `N = p * q` in `poly(log N)` steps.

* **Fact 1 (CRT-split collision is the only reveal mechanism).**
  For `N = p * q` with `p ≠ q` prime and any integer `d`,
  `gcd d N` is a *nontrivial* divisor of `N` if and only if **exactly one** of
  `p ∣ d`, `q ∣ d` holds (`crt_reveal_iff`).  Applied to `d = x t - x s` along a
  trajectory this says: a factor appears exactly when two trajectory values agree
  on **one** CRT component.

* **Fact 2 (`N`-explicit maps do not split the CRT).**
  An `N`-explicit map is a polynomial with integer coefficients (ring operations and
  constants manufactured from the digits of `N`).  Its orbit reduced mod `p` is the
  orbit of the *reduced* polynomial started at the *reduced* seed
  (`polyOrbit_cast`, `modOrbit_congr`): the mod-`p` dynamics depends on nothing
  except `f mod p` and `x₀ mod p`.  In particular the map itself carries no
  information about which of the two CRT components it is being run in.

* **Consequence.** The factor-revealing event in any such iteration is *exactly* an
  exclusive mod-`p` / mod-`q` cycle closure (`reveal_iff_xor_closure`), and no reveal
  can happen before the first closure (`no_reveal_before_closure`).  Closures do
  exist, but the only unconditional guarantee is the pigeonhole bound `t ≤ p`
  (`exists_closure_le`), and after a closure the orbit is eventually periodic
  (`modOrbit_eventually_periodic`) — the rho shape.

Quantitative lower bounds for the three regimes are in `CRTSplitNoGoBounds.lean`.
-/

open CRTSplitNoGo

open Polynomial

/-! ## Fact 1: a nontrivial gcd is exactly an exclusive CRT collision -/


/-- For a divisor `r` of `N`, `r` divides `gcd d N` iff `r` divides `d`. -/
lemma dvd_gcd_iff_of_dvd {N : ℕ} {d : ℤ} {r : ℕ} (hrN : r ∣ N) :
    r ∣ Int.gcd d (N : ℤ) ↔ (r : ℤ) ∣ d := by
  constructor
  · intro h
    have : ((r : ℕ) : ℤ) ∣ ((Int.gcd d (N : ℤ) : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    exact this.trans (Int.gcd_dvd_left d (N : ℤ))
  · intro h
    have hrN' : (r : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr hrN
    exact Int.dvd_gcd h hrN'


/-! ## Fact 2: an `N`-explicit map is functorial for reduction mod `p` -/









/-! ## Consequence: the reveal event is an exclusive mod-`p` cycle closure -/




/-! ## The rho shape: closures exist, but pigeonhole only gives `t ≤ p` -/




open CRTSplitNoGo in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (d : ℤ) :
    RevealsFactor (p * q) d ↔ Xor' ((p : ℤ) ∣ d) ((q : ℤ) ∣ d) := by
  have hppos : 0 < p := hp.pos
  have hqpos : 0 < q := hq.pos
  have hNpos : 0 < p * q := Nat.mul_pos hppos hqpos
  set g : ℕ := Int.gcd d ((p * q : ℕ) : ℤ) with hg
  have hgN : g ∣ p * q := by
    have : ((g : ℕ) : ℤ) ∣ ((p * q : ℕ) : ℤ) := Int.gcd_dvd_right d ((p * q : ℕ) : ℤ)
    exact Int.ofNat_dvd.mp this
  have hgle : g ≤ p * q := Nat.le_of_dvd hNpos hgN
  have hpdvdN : p ∣ p * q := Dvd.intro q rfl
  have hqdvdN : q ∣ p * q := Dvd.intro_left p rfl
  have hP : p ∣ g ↔ (p : ℤ) ∣ d := dvd_gcd_iff_of_dvd hpdvdN
  have hQ : q ∣ g ↔ (q : ℤ) ∣ d := dvd_gcd_iff_of_dvd hqdvdN
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  rw [← hP, ← hQ]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hpg : p ∣ g
    · refine Or.inl ⟨hpg, ?_⟩
      intro hqg
      have : p * q ∣ g := hcop.mul_dvd_of_dvd_of_dvd hpg hqg
      have := Nat.le_of_dvd (by omega) this
      omega
    · by_cases hqg : q ∣ g
      · exact Or.inr ⟨hqg, hpg⟩
      · -- neither prime divides `g`, so `g` is coprime to `N` and hence `g = 1`
        exfalso
        have hcp : Nat.Coprime g p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpg))
        have hcq : Nat.Coprime g q := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqg))
        have : Nat.Coprime g (p * q) := Nat.Coprime.mul_right hcp hcq
        have hg1 : g = 1 := this.eq_one_of_dvd hgN
        omega
  · intro h
    rcases h with ⟨hpg, hqg⟩ | ⟨hqg, hpg⟩
    · have hgpos : 0 < g := by
        rcases Nat.eq_zero_or_pos g with h0 | h0
        · exfalso; rw [h0] at hgN; exact absurd (Nat.eq_zero_of_zero_dvd hgN) (by omega)
        · exact h0
      have h1 : 1 < g := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hgpos hpg)
      refine ⟨h1, ?_⟩
      rcases lt_or_eq_of_le hgle with h | h
      · exact h
      · exact absurd (h ▸ hqdvdN) hqg
    · have hgpos : 0 < g := by
        rcases Nat.eq_zero_or_pos g with h0 | h0
        · exfalso; rw [h0] at hgN; exact absurd (Nat.eq_zero_of_zero_dvd hgN) (by omega)
        · exact h0
      have h1 : 1 < g := lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd hgpos hqg)
      refine ⟨h1, ?_⟩
      rcases lt_or_eq_of_le hgle with h | h
      · exact h
      · exact absurd (h ▸ hpdvdN) hpg
