-- Prove2me | Definitions.Def_Novelty_NoPinningSymmetry
-- name    : Novelty_NoPinningSymmetry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:34:35.302451+00:00
-- url     : https://prove2.me/theorems/3653e53f-19ab-435c-9f92-c8bc80b6a795
-- title:
--   Aether Catalog definitions — Novelty_NoPinningSymmetry
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NoPinningSymmetry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NoPinningSymmetry.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_NoPinningLemma
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


namespace Novelty.NoPinning

/-! ## What the data does determine: the partner class -/


/-! ## The compensation involution -/

/-- The compensation map on unit classes: `x ↦ u · x⁻¹`, where `u` is the class
of the target `N₀`.  It sends the class of one factor to the class of the
other. -/
def partnerEquiv {L : ℕ} (u : (ZMod L)ˣ) : (ZMod L)ˣ ≃ (ZMod L)ˣ where
  toFun x := u * x⁻¹
  invFun x := u * x⁻¹
  left_inv x := by simp
  right_inv x := by simp




/-! ## Full support: every unit class is consistent -/


/-! ## Partial factorisations are not excluded either -/




end Novelty.NoPinning


