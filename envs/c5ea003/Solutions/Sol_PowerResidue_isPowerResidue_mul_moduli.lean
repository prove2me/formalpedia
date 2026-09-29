-- Prove2me | solution 1 for PowerResidue.isPowerResidue_mul_moduli
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:08:30.637861+00:00
-- url     : https://prove2.me/submissions/da7030c7-a9cd-4bdb-9b04-b29df88a2229

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









open PowerResidue in
theorem solution{k m n a : ℕ} (h : Nat.Coprime m n) :
    IsPowerResidue k (m * n) a ↔ IsPowerResidue k m a ∧ IsPowerResidue k n a := by
  classical
  have e := ZMod.chineseRemainder (m := m) (n := n) h
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨⟨(ZMod.castHom (show m ∣ m * n from Dvd.intro n rfl) (ZMod m)) b, ?_⟩,
            ⟨(ZMod.castHom (show n ∣ m * n from Dvd.intro_left m rfl) (ZMod n)) b, ?_⟩⟩
    · rw [← map_pow, hb, map_natCast]
    · rw [← map_pow, hb, map_natCast]
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨e.symm (x, y), ?_⟩
    have hcast : e ((a : ZMod (m * n))) = ((a : ZMod m), (a : ZMod n)) := by
      rw [map_natCast]; rfl
    apply e.injective
    rw [map_pow, RingEquiv.apply_symm_apply, hcast]
    exact Prod.ext (by simpa using hx) (by simpa using hy)
