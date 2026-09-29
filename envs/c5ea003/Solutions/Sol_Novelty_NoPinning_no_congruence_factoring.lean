-- Prove2me | solution 1 for Novelty.NoPinning.no_congruence_factoring
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:24:43.225725+00:00
-- url     : https://prove2.me/submissions/162c8746-eff4-424d-8b40-893ead714144

-- Sol generated from Novelty/NoPinningNoFactoring.lean
import Mathlib
import Definitions.Def_Novelty_NoPinningLemma
import Theorems.Thm_Novelty_NoPinning_exists_two_coprime_semiprimes_same_class
import Theorems.Thm_Novelty_NoPinning_odd_of_coprime_of_two_dvd
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
theorem solution(L : ℕ) [NeZero L] (h2 : 2 ∣ L)
    {β : Type} (f : ℕ → β) (hf : IsModObs L f) (A : β → ℕ) :
    ¬ (∀ p q : ℕ, p.Prime → q.Prime → Nat.Coprime (p * q) L →
        A (f (p * q)) ∣ p * q ∧ 1 < A (f (p * q))) := by
  intro hA
  obtain ⟨p₁, q₁, p₂, q₂, hp₁, hq₁, hp₂, hq₂, hc₁, hc₂, hcop, hmod⟩ :=
    exists_two_coprime_semiprimes_same_class L
  have hodd₁ : Odd (p₁ * q₁) := odd_of_coprime_of_two_dvd h2 hc₁
  have hodd₂ : Odd (p₂ * q₂) := odd_of_coprime_of_two_dvd h2 hc₂
  have hsame : f (p₁ * q₁) = f (p₂ * q₂) := hf hodd₁ hodd₂ hmod
  obtain ⟨hdvd₁, hgt₁⟩ := hA p₁ q₁ hp₁ hq₁ hc₁
  obtain ⟨hdvd₂, -⟩ := hA p₂ q₂ hp₂ hq₂ hc₂
  rw [hsame] at hdvd₁ hgt₁
  have : A (f (p₂ * q₂)) ∣ Nat.gcd (p₁ * q₁) (p₂ * q₂) := Nat.dvd_gcd hdvd₁ hdvd₂
  rw [hcop] at this
  have := Nat.dvd_one.mp this
  omega
