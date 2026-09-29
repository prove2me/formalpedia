-- Prove2me | solution 1 for PowerResidue.card_image_resVec_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:04:03.21383+00:00
-- url     : https://prove2.me/submissions/e58fa6ba-41f6-4970-a0e7-612e1ffda839

-- Sol generated from Combinatorics/PowerResidueCriterion.lean
import Mathlib
import Definitions.Def_Combinatorics_PowerResidueCriterion
/-
# Higher power residues: the criterion, the tower, and the capacity of a symbol channel

Formal core for `39_PowerResidue_Circularity.md` (experiment KPOWER, #374).

The KPOWER experiment asks whether **cubic** (`Z[ω]`) or **quartic** (`Z[i]`)
power-residue symbols give a *residue dial* — a `poly(log N)`-computable,
periodic statistic of a secret prime `p` — that is strictly stronger than the
quadratic (Kronecker/Jacobi) channel already analysed in
`Combinatorics.DialThresholdNoAmplification`.

This file builds the algebraic core needed to answer that question:

* `PowerResidue.exists_pow_eq_iff_pow_card_div` — the **`k`-th power criterion**
  in an arbitrary finite cyclic group: for `k ∣ |G|`, `x` is a `k`-th power iff
  `x ^ (|G| / k) = 1`.  This is the structural heart; Euler's criterion
  (`k = 2`) and the cubic/quartic symbols are instances.
* `PowerResidue.zmod_exists_pow_eq_iff`, `PowerResidue.isPowerResidue_iff_pow` —
  its transfer to `(ZMod p)ˣ` for a prime `p`, i.e. the definition of the
  symbol `(a | p)_k = a ^ ((p-1)/k)` as a *residuacity test*.
* `PowerResidue.isPowerResidue_of_dvd` — the **residuacity tower**: `l`-th power
  residues are `k`-th power residues whenever `k ∣ l`.  Cubic data therefore
  *contains* no quadratic data and vice versa; the channels are nested only
  along divisibility.
* `PowerResidue.isPowerResidue_mul_moduli` — the **CRT factorisation** of
  residuacity at a composite modulus `N = m·n`: the `N`-computable predicate is
  exactly the *conjunction* of the two local predicates, hence a **symmetric**
  function of the factor pair.  This is barrier 2 in algebraic form: the only
  higher-power datum an attacker can compute from `N` alone is symmetric in
  `p` and `q`.
* `PowerResidue.card_image_le_pow`, `PowerResidue.card_le_two_pow_of_injOn`,
  `PowerResidue.log_le_of_separating` — the **capacity** of a `K`-symbol
  fingerprint.  Whatever the exponent `k`, a length-`K` residuacity fingerprint
  takes at most `2 ^ K` values and therefore separates at most `2 ^ K`
  candidates: `K ≥ log₂ C` symbols are needed to pin `C` candidates.  The bound
  does not depend on `k`, which is the formal content of the experiment's
  "leakage saturates like quadratic".

The circularity itself — computing `a ^ ((p-1)/k)` presupposes `p` — and the
failure of the cubic symbol to be periodic in `p` are proved in
`Combinatorics.PowerResidueCircularity`.
-/

open PowerResidue

open Finset

/-! ## 1. The `k`-th power criterion in a finite cyclic group

Everything downstream is an instance of this single statement.  Note that no
primality, no field structure, and no root of unity is involved: it is pure
cyclic group theory, which is why it applies verbatim to the cubic and quartic
symbols. -/



/-! ## 2. Residuacity as a predicate on natural numbers -/








/-! ## 3. Barrier 2 in algebraic form: `N`-computable residuacity is symmetric

For a composite modulus the residuacity predicate factors through the Chinese
Remainder Theorem into the *conjunction* of the local predicates.  Hence the
only higher-power information an attacker can extract from `N = p·q` without
factoring is a symmetric function of `p` and `q`: it cannot single out a
factor. -/



/-! ## 4. Capacity of a `K`-symbol fingerprint: the same for every exponent `k`

The experiment reports that cubic and quadratic fingerprints separate candidate
primes at the *same* rate.  Here is the reason, in its sharpest form: a
residuacity fingerprint of length `K` is a vector of `K` bits, whatever the
exponent, so it takes at most `2 ^ K` values.  Raising `k` buys nothing. -/

variable {K : ℕ}

/-- A fingerprint with values in a fixed finite type takes at most
`(card β) ^ K` values on any candidate set. -/
theorem card_image_le_pow {α β : Type*} [DecidableEq β] [Fintype β] [DecidableEq α]
    (S : Finset α) (f : α → (Fin K → β)) :
    (S.image f).card ≤ (Fintype.card β) ^ K := by
  classical
  calc (S.image f).card ≤ (Finset.univ : Finset (Fin K → β)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (Fin K → β) := rfl
    _ = (Fintype.card β) ^ K := by simp








open PowerResidue in
open scoped Classical in
theorem solution(k : ℕ) (bases : Fin K → ℕ) (S : Finset ℕ) :
    (S.image (resVec k bases)).card ≤ 2 ^ K := by
  simpa using card_image_le_pow (β := Bool) S (resVec k bases)
