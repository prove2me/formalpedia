-- Prove2me | solution 1 for Novelty.NoPinning.fullBattery_isModObs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:23:24.843676+00:00
-- url     : https://prove2.me/submissions/a1af6108-2942-4ff1-9e92-4b449cc62ed0

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



/-! ## The three observable channels -/




theorem isModObs_residueObs {L m : ℕ} (h : m ∣ L) : IsModObs L (residueObs m) := by
  intro a b _ _ hab
  simp only [residueObs, Nat.cast_inj]
  exact hab.of_dvd h

theorem isModObs_gcdObs {L c : ℕ} (h : c ∣ L) : IsModObs L (gcdObs c) := by
  intro a b _ _ hab
  simp only [gcdObs, Nat.cast_inj]
  exact (hab.of_dvd h).gcd_eq

theorem isModObs_jacobiObs {L a : ℕ} (h : 4 * a ∣ L) : IsModObs L (jacobiObs a) := by
  intro m n hm hn hmn
  simp only [jacobiObs]
  rw [jacobiSym.mod_right' a hm, jacobiSym.mod_right' a hn, hmn.of_dvd h]




/-! ## The pinned set at level `B` -/





/-! ## Barrier 1: polynomial gcds are functions of `N` -/



/-! ## A concrete instance -/



open Novelty.NoPinning in
theorem solution(B : ℕ) :
    ∀ f ∈ fullBattery B, IsModObs (modLevel B) f := by
  intro f hf
  have hdvd : ∀ i : ℕ, i < B → (i + 1) ∣ lcmUpTo B := fun i hi =>
    dvd_lcmUpTo (Nat.le_add_left 1 i) (by omega)
  simp only [fullBattery, List.mem_append, List.mem_map, List.mem_range] at hf
  rcases hf with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · exact isModObs_residueObs (dvd_trans (hdvd i hi) ⟨4, by rw [modLevel]; ring⟩)
  · exact isModObs_jacobiObs (mul_dvd_mul_left 4 (hdvd i hi))
  · exact isModObs_gcdObs (dvd_trans (hdvd i hi) ⟨4, by rw [modLevel]; ring⟩)
