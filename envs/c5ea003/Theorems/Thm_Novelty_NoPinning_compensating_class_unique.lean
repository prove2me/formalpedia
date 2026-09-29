-- Prove2me | Theorems.Thm_Novelty_NoPinning_compensating_class_unique
-- name    : Novelty.NoPinning.compensating_class_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:15:16.948124+00:00
-- url     : https://prove2.me/theorems/dbecc2d3-f023-493f-abb9-a8657601730a
-- title:
--   Uniqueness of the partner class.
-- statement:
--   **Uniqueness of the partner class.**  Two compensating partners of the same
--   candidate `p` (coprime to `L`) are congruent modulo `L`.  A modulus-`L` battery
--   thus pins the cofactor's *residue class* exactly — and nothing more.
--
--   ```lean
--   theorem Novelty.NoPinning.compensating_class_unique{L : ℕ} [NeZero L] {N₀ p q q' : ℕ}
--       (hp : Nat.Coprime p L) (h : p * q ≡ N₀ [MOD L]) (h' : p * q' ≡ N₀ [MOD L]) :
--       q ≡ q' [MOD L] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NoPinningSymmetry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NoPinningSymmetry.lean#L34

-- Thm stub generated from Novelty/NoPinningSymmetry.lean
import Mathlib
import Definitions.Def_Novelty_NoPinningLemma
import Definitions.Def_Novelty_NoPinningSymmetry
/-
# Symmetry of the compensation map, and no-pinning for partial factorisations

Third companion to `Novelty/NoPinningLemma.lean`.  The no-pinning lemma says the
modulus-`L` data never excludes a candidate.  Here we describe *exactly what the
data does determine* — the partner class — and show that the group-theoretic
picture behind it is a single involution of `(ZMod L)ˣ`.

## Main results

* `compensating_class_unique` — the battery **does** determine the residue class
  of the cofactor: any two compensating partners of the same candidate are
  congruent mod `L`.  The pinning failure is therefore not a loss of
  information, but the fact that each class contains infinitely many primes.
* `partnerEquiv`, `partnerEquiv_involutive` — the compensation map
  `x ↦ N₀ · x⁻¹` is an involutive permutation of `(ZMod L)ˣ`; it exchanges the
  classes of the two factors, which is the "symmetric function of `(p,q)`"
  phenomenon (barrier 2) in group-theoretic form.
* `consistent_classes_eq_univ` — **full support**: every unit class of `ZMod L`
  contains a prime `p` that is consistent with the target, i.e. that has a prime
  partner `q` with `p·q ≡ N₀`.  The consistent set is the entire unit group.
* `no_pinning_of_partial_factorization` — no modulus-`L` battery can even
  exclude a *prescribed partial factorisation*: for any finite list of
  candidate factors coprime to `L`, infinitely many primes `q` complete it to a
  number with exactly the observed data.
-/


open Novelty.NoPinning

/-! ## What the data does determine: the partner class -/

theorem Novelty.NoPinning.compensating_class_unique{L : ℕ} [NeZero L] {N₀ p q q' : ℕ}
    (hp : Nat.Coprime p L) (h : p * q ≡ N₀ [MOD L]) (h' : p * q' ≡ N₀ [MOD L]) :
    q ≡ q' [MOD L] := by sorry
