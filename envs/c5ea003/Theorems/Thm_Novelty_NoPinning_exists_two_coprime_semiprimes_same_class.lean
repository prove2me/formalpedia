-- Prove2me | Theorems.Thm_Novelty_NoPinning_exists_two_coprime_semiprimes_same_class
-- name    : Novelty.NoPinning.exists_two_coprime_semiprimes_same_class
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:15:42.361856+00:00
-- url     : https://prove2.me/theorems/083d797c-0a87-4fc5-bf41-895248decb47
-- title:
--   Four distinct primes coprime to `L` producing two coprime semiprimes in the
-- statement:
--   Four distinct primes coprime to `L` producing two coprime semiprimes in the
--   same class mod `L`.  The two semiprimes are indistinguishable for every
--   modulus-`L` observable, yet share no factor.
--
--   ```lean
--   theorem Novelty.NoPinning.exists_two_coprime_semiprimes_same_class(L : ℕ) [NeZero L] :
--       ∃ p₁ q₁ p₂ q₂ : ℕ, p₁.Prime ∧ q₁.Prime ∧ p₂.Prime ∧ q₂.Prime ∧
--         Nat.Coprime (p₁ * q₁) L ∧ Nat.Coprime (p₂ * q₂) L ∧
--         Nat.Coprime (p₁ * q₁) (p₂ * q₂) ∧
--         p₁ * q₁ ≡ p₂ * q₂ [MOD L] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NoPinningNoFactoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NoPinningNoFactoring.lean#L32

-- Thm stub generated from Novelty/NoPinningNoFactoring.lean
import Mathlib
import Definitions.Def_Novelty_NoPinningLemma
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

theorem Novelty.NoPinning.exists_two_coprime_semiprimes_same_class(L : ℕ) [NeZero L] :
    ∃ p₁ q₁ p₂ q₂ : ℕ, p₁.Prime ∧ q₁.Prime ∧ p₂.Prime ∧ q₂.Prime ∧
      Nat.Coprime (p₁ * q₁) L ∧ Nat.Coprime (p₂ * q₂) L ∧
      Nat.Coprime (p₁ * q₁) (p₂ * q₂) ∧
      p₁ * q₁ ≡ p₂ * q₂ [MOD L] := by sorry
