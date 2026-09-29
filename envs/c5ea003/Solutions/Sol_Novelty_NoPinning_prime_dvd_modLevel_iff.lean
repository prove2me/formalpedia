-- Prove2me | solution 1 for Novelty.NoPinning.prime_dvd_modLevel_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:24:44.562997+00:00
-- url     : https://prove2.me/submissions/b4f20dbe-df0f-4ad6-8ffc-63727bf6b1a5

-- Sol generated from Novelty/NoPinningBattery.lean
import Mathlib
import Definitions.Def_Novelty_NoPinningBattery
import Definitions.Def_Novelty_NoPinningLemma
/-
# The poly(log N) battery: residues, Jacobi symbols and gcds

Companion to `Novelty/NoPinningLemma.lean`.  Here we exhibit the concrete
`poly(log N)`-computable battery of the COMPENSATING-PARTNER experiment as a
family of modulus-`L` observables, with `L = modLevel B = 4 · lcm(1,…,B)`:

* `residueObs m : N ↦ N mod m` for `1 ≤ m ≤ B`,
* `jacobiObs a : N ↦ (a | N)` (Jacobi symbol) for `1 ≤ a ≤ B`,
* `gcdObs c : N ↦ gcd(N, c)` for `1 ≤ c ≤ B`.

and we prove:

* `isModObs_residueObs`, `isModObs_jacobiObs`, `isModObs_gcdObs` — each channel
  is a modulus-`L` observable;
* `fullBattery_no_pinning` — the entire battery is blind: for every target `N₀`
  and every candidate prime `p` coprime to `L` there are infinitely many primes
  `q` with identical battery readouts on `p·q` and `N₀`;
* `prime_dvd_modLevel_iff` — the pinned primes at level `B` are exactly the
  primes `≤ B` (plus `2`), so `card ≤ B`: `poly(log N)` many;
* `large_prime_never_pinned` — every prime candidate `p > B` survives;
* `Int.gcd_eval_eq_gcd_coeff_zero` — **barrier 1**: `gcd(f(N), N) = gcd(f(0), N)`
  for every integer polynomial `f`; polynomial gcds are functions of `N` alone
  and add no pinning power.  In particular `gcd(N + k, N) = gcd(k, N)`.
-/


open Novelty.NoPinning

/-! ## The modulus of a level-`B` battery -/




theorem dvd_lcmUpTo {B m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ B) : m ∣ lcmUpTo B := by
  have : m ∈ Finset.Icc 1 B := Finset.mem_Icc.2 ⟨h1, h2⟩
  simpa [lcmUpTo] using Finset.dvd_lcm (f := (id : ℕ → ℕ)) this


instance (B : ℕ) : NeZero (modLevel B) := ⟨modLevel_ne_zero B⟩

theorem four_dvd_modLevel (B : ℕ) : 4 ∣ modLevel B := ⟨lcmUpTo B, rfl⟩


/-! ## The three observable channels -/










/-! ## The pinned set at level `B` -/

theorem lcmUpTo_dvd_prod (B : ℕ) : lcmUpTo B ∣ ∏ i ∈ Finset.Icc 1 B, i :=
  Finset.lcm_dvd fun _ hi => Finset.dvd_prod_of_mem _ hi




/-! ## Barrier 1: polynomial gcds are functions of `N` -/



/-! ## A concrete instance -/



open Novelty.NoPinning in
theorem solution{B p : ℕ} (hp : p.Prime) :
    p ∣ modLevel B ↔ (p = 2 ∨ p ≤ B) := by
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h4 | hlcm
    · left
      have : p ∣ 2 ^ 2 := by simpa using h4
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
      exact this
    · right
      have hprod : p ∣ ∏ i ∈ Finset.Icc 1 B, i := hlcm.trans (lcmUpTo_dvd_prod B)
      obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finset_prod_iff hp.prime id).1 hprod
      have hiB := (Finset.mem_Icc.1 hi).2
      have hi1 := (Finset.mem_Icc.1 hi).1
      have hpi' : p ∣ i := by simpa using hpi
      exact le_trans (Nat.le_of_dvd (by omega) hpi') hiB
  · rintro (rfl | hpB)
    · exact dvd_trans ⟨2, rfl⟩ (four_dvd_modLevel B)
    · exact dvd_trans (dvd_lcmUpTo hp.one_lt.le hpB) ⟨4, by rw [modLevel]; ring⟩
