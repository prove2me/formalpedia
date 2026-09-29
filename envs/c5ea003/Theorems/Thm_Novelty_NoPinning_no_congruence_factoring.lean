-- Prove2me | Theorems.Thm_Novelty_NoPinning_no_congruence_factoring
-- name    : Novelty.NoPinning.no_congruence_factoring
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:15:58.149147+00:00
-- url     : https://prove2.me/theorems/52a5a8a2-b56b-40dd-8e66-4fd1aad17bfe
-- title:
--   No factoring from congruence data.
-- statement:
--   **No factoring from congruence data.**  Fix any modulus `L` with `2 ∣ L`,
--   any observable `f` of modulus `L` (all residues, Jacobi symbols and gcds of the
--   poly(log N) battery are of this form) and any decoding map `A` from readouts to
--   naturals.  Then `A ∘ f` cannot return a nontrivial divisor of every semiprime
--   coprime to `L`: some semiprime `p·q` has `A (f (p*q))` either failing to divide
--   `p*q`, or equal to `1` or less.
--
--   This is the unconditional "poly-computable ⇒ no-pinning ⇒ cannot factor" half of
--   the barrier programme, and it holds for arbitrarily large moduli `L`.
--
--   ```lean
--   theorem Novelty.NoPinning.no_congruence_factoring(L : ℕ) [NeZero L] (h2 : 2 ∣ L)
--       {β : Type} (f : ℕ → β) (hf : IsModObs L f) (A : β → ℕ) :
--       ¬ (∀ p q : ℕ, p.Prime → q.Prime → Nat.Coprime (p * q) L →
--           A (f (p * q)) ∣ p * q ∧ 1 < A (f (p * q))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NoPinningNoFactoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NoPinningNoFactoring.lean#L66

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

theorem Novelty.NoPinning.no_congruence_factoring(L : ℕ) [NeZero L] (h2 : 2 ∣ L)
    {β : Type} (f : ℕ → β) (hf : IsModObs L f) (A : β → ℕ) :
    ¬ (∀ p q : ℕ, p.Prime → q.Prime → Nat.Coprime (p * q) L →
        A (f (p * q)) ∣ p * q ∧ 1 < A (f (p * q))) := by sorry
