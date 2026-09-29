-- Prove2me | solution 1 for Novelty.NoPinning.exists_two_coprime_semiprimes_same_class
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:23:24.244091+00:00
-- url     : https://prove2.me/submissions/3e0027d4-86b7-4102-b8c5-ee14e1a3552b

-- Sol generated from Novelty/NoPinningNoFactoring.lean
import Mathlib
import Definitions.Def_Novelty_NoPinningLemma
import Theorems.Thm_Novelty_NoPinning_infinite_compensating_primes
import Theorems.Thm_Novelty_NoPinning_unpinnedPrimes_infinite
/-
# From no-pinning to no-factoring

Fourth companion to `Novelty/NoPinningLemma.lean`.  The no-pinning lemma is a
statement about candidates; here we convert it into an *unconditional
impossibility statement about algorithms*: no map whose input is the readout of
a modulus-`L` battery can output a nontrivial factor of every semiprime, for
**any** modulus `L` whatsoever — not merely for `poly(log N)`-sized moduli.

The mechanism is the compensating-partner lemma applied twice: a single residue
class contains two *coprime* semiprimes `p₁q₁` and `p₂q₂`, so a nontrivial
divisor computed from the class alone would have to divide two coprime numbers.

## Main results

* `exists_two_coprime_semiprimes_same_class` — every modulus `L` admits two
  coprime semiprimes with the same residue mod `L` (built from four distinct
  primes coprime to `L`).
* `no_congruence_factoring` — **main theorem**: for any modulus `L` with
  `2 ∣ L`, any observable `f` of modulus `L` and any decoding map `A`, the pair
  `(f, A)` fails to produce a nontrivial divisor for some semiprime coprime to
  `L`.
* `no_residue_factoring` — the special case `f = (· % L)`, i.e. the strongest
  possible congruence battery.
-/


open Novelty.NoPinning






open Novelty.NoPinning in
theorem solution(L : ℕ) [NeZero L] :
    ∃ p₁ q₁ p₂ q₂ : ℕ, p₁.Prime ∧ q₁.Prime ∧ p₂.Prime ∧ q₂.Prime ∧
      Nat.Coprime (p₁ * q₁) L ∧ Nat.Coprime (p₂ * q₂) L ∧
      Nat.Coprime (p₁ * q₁) (p₂ * q₂) ∧
      p₁ * q₁ ≡ p₂ * q₂ [MOD L] := by
  have hL : L ≠ 0 := NeZero.ne L
  have hS := unpinnedPrimes_infinite L hL
  -- pick `p₁`
  obtain ⟨p₁, ⟨hp₁, hp₁L⟩, -⟩ := hS.exists_gt 0
  have hcop₁ : Nat.Coprime p₁ L := (Nat.Prime.coprime_iff_not_dvd hp₁).2 hp₁L
  -- pick `q₁ > p₁`
  obtain ⟨q₁, ⟨hq₁, hq₁L⟩, hq₁gt⟩ := hS.exists_gt p₁
  have hcopq₁ : Nat.Coprime q₁ L := (Nat.Prime.coprime_iff_not_dvd hq₁).2 hq₁L
  -- pick `p₂ > q₁`
  obtain ⟨p₂, ⟨hp₂, hp₂L⟩, hp₂gt⟩ := hS.exists_gt q₁
  have hcop₂ : Nat.Coprime p₂ L := (Nat.Prime.coprime_iff_not_dvd hp₂).2 hp₂L
  have hN₀ : Nat.Coprime (p₁ * q₁) L := Nat.Coprime.mul_left hcop₁ hcopq₁
  -- pick a compensating prime `q₂ > p₂`
  obtain ⟨q₂, ⟨hq₂, hcopq₂, hmod⟩, hq₂gt⟩ :=
    (infinite_compensating_primes L hN₀ hcop₂).exists_gt p₂
  refine ⟨p₁, q₁, p₂, q₂, hp₁, hq₁, hp₂, hq₂, hN₀,
    Nat.Coprime.mul_left hcop₂ hcopq₂, ?_, hmod.symm⟩
  have hne : ∀ {a b : ℕ}, a.Prime → b.Prime → a ≠ b → Nat.Coprime a b :=
    fun ha hb hab => (Nat.coprime_primes ha hb).2 hab
  have h₁₂ : p₁ ≠ p₂ := by omega
  have h₁₃ : p₁ ≠ q₂ := by omega
  have h₂₂ : q₁ ≠ p₂ := by omega
  have h₂₃ : q₁ ≠ q₂ := by omega
  exact Nat.Coprime.mul_left (Nat.Coprime.mul_right (hne hp₁ hp₂ h₁₂) (hne hp₁ hq₂ h₁₃))
    (Nat.Coprime.mul_right (hne hq₁ hp₂ h₂₂) (hne hq₁ hq₂ h₂₃))
