-- Prove2me | Definitions.Def_Novelty_NoPinningBattery
-- name    : Novelty_NoPinningBattery
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:34:23.508003+00:00
-- url     : https://prove2.me/theorems/4b60829b-1227-466d-adad-2e8a896d34ac
-- title:
--   Aether Catalog definitions — Novelty_NoPinningBattery
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NoPinningBattery`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NoPinningBattery.lean by skeleton subtraction
import Mathlib
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


namespace Novelty.NoPinning

/-! ## The modulus of a level-`B` battery -/

/-- `lcm(1, …, B)`. -/
def lcmUpTo (B : ℕ) : ℕ := (Finset.Icc 1 B).lcm id

/-- The modulus of the level-`B` battery: `4 · lcm(1,…,B)`.  The factor `4`
accommodates the conductor of the Jacobi symbols. -/
def modLevel (B : ℕ) : ℕ := 4 * lcmUpTo B

theorem lcmUpTo_ne_zero (B : ℕ) : lcmUpTo B ≠ 0 := by
  unfold lcmUpTo
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  simp only [Finset.mem_Icc, id_eq] at h
  obtain ⟨m, hm, hm0⟩ := h
  omega


theorem modLevel_ne_zero (B : ℕ) : modLevel B ≠ 0 :=
  mul_ne_zero (by norm_num) (lcmUpTo_ne_zero B)

instance (B : ℕ) : NeZero (modLevel B) := ⟨modLevel_ne_zero B⟩



/-! ## The three observable channels -/

/-- Residue channel: `N ↦ N mod m`. -/
def residueObs (m : ℕ) : ℕ → ℤ := fun N => (N % m : ℕ)

/-- Jacobi channel: `N ↦ (a | N)`. -/
def jacobiObs (a : ℕ) : ℕ → ℤ := fun N => jacobiSym (a : ℤ) N

/-- gcd channel: `N ↦ gcd(N, c)`. -/
def gcdObs (c : ℕ) : ℕ → ℤ := fun N => (Nat.gcd N c : ℕ)




/-- The level-`B` battery: all residues, Jacobi symbols and gcds with parameter
in `{1, …, B}`.  Every entry is computable in `poly(log N)` time. -/
def fullBattery (B : ℕ) : List (ℕ → ℤ) :=
  (List.range B).map (fun i => residueObs (i + 1)) ++
  (List.range B).map (fun i => jacobiObs (i + 1)) ++
  (List.range B).map (fun i => gcdObs (i + 1))



/-! ## The pinned set at level `B` -/





/-! ## Barrier 1: polynomial gcds are functions of `N` -/



/-! ## A concrete instance -/


end Novelty.NoPinning


