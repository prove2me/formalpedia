-- Prove2me | solution 1 for Novelty.NoPinning.compensating_class_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:20:41.093403+00:00
-- url     : https://prove2.me/submissions/4669988c-27a3-4830-a58b-60fdb578cef4

-- Sol generated from Novelty/NoPinningSymmetry.lean
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


/-! ## The compensation involution -/





/-! ## Full support: every unit class is consistent -/


/-! ## Partial factorisations are not excluded either -/





open Novelty.NoPinning in
theorem solution{L : ℕ} [NeZero L] {N₀ p q q' : ℕ}
    (hp : Nat.Coprime p L) (h : p * q ≡ N₀ [MOD L]) (h' : p * q' ≡ N₀ [MOD L]) :
    q ≡ q' [MOD L] := by
  have hpu : IsUnit ((p : ZMod L)) := (ZMod.isUnit_iff_coprime p L).2 hp
  have h1 : ((p : ZMod L)) * (q : ZMod L) = ((p : ZMod L)) * (q' : ZMod L) := by
    have e1 : ((p * q : ℕ) : ZMod L) = (N₀ : ZMod L) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 h
    have e2 : ((p * q' : ℕ) : ZMod L) = (N₀ : ZMod L) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 h'
    push_cast at e1 e2
    rw [e1, e2]
  have hcancel : (q : ZMod L) = (q' : ZMod L) := by
    obtain ⟨u, hu⟩ := hpu
    rw [← hu] at h1
    exact (Units.mul_right_inj u).mp h1
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hcancel
