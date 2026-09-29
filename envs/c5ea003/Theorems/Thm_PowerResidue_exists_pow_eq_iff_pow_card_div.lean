-- Prove2me | Theorems.Thm_PowerResidue_exists_pow_eq_iff_pow_card_div
-- name    : PowerResidue.exists_pow_eq_iff_pow_card_div
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:23:37.963809+00:00
-- url     : https://prove2.me/theorems/59849d04-72b9-465f-9d1b-28bec9e11704
-- title:
--   The `k`-th power criterion.
-- statement:
--   **The `k`-th power criterion.**  In a finite cyclic group `G`, if `k` divides
--   `|G|`, then `x` is a `k`-th power exactly when `x ^ (|G| / k) = 1`.
--
--   For `G = (ZMod p)ˣ` and `k = 2` this is Euler's criterion; for `k = 3` it is the
--   cubic residue symbol `(a | p)₃`, for `k = 4` the quartic symbol.
--
--   ```lean
--   theorem PowerResidue.exists_pow_eq_iff_pow_card_div{G : Type*} [CommGroup G] [Fintype G] [IsCyclic G]
--       {k : ℕ} (hk : k ∣ Fintype.card G) (x : G) :
--       (∃ y : G, y ^ k = x) ↔ x ^ (Fintype.card G / k) = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/PowerResidueCriterion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/PowerResidueCriterion.lean#L55

-- Thm stub generated from Combinatorics/PowerResidueCriterion.lean
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

theorem PowerResidue.exists_pow_eq_iff_pow_card_div{G : Type*} [CommGroup G] [Fintype G] [IsCyclic G]
    {k : ℕ} (hk : k ∣ Fintype.card G) (x : G) :
    (∃ y : G, y ^ k = x) ↔ x ^ (Fintype.card G / k) = 1 := by sorry
