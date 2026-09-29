-- Prove2me | solution 1 for UniversalPosets.isUniversalPosetOfSize_of_host
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:30:00.678881+00:00
-- url     : https://prove2.me/submissions/577948ee-3433-49f9-bc49-a0d114b42bfa

-- Sol generated from Cryptography/UniversalPosets/MinSize.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_Bounds
import Definitions.Def_Cryptography_UniversalPosets_MinSize

/-!
# The universal-poset size function `U(n)`

This file packages the bounds of `Bounds.lean` and `SmallCases.lean` into a
single numerical invariant:

`minUniversalSize n` is the least `N` such that some partial order on `N` points
contains every partial order on `n` points as an induced subposet.

Proved here:

* `minUniversalSize_le_two_pow`   :  `U(n) ≤ 2 ^ n`   (Boolean lattice);
* `self_le_minUniversalSize`      :  `n ≤ U(n)`       (the `n`-antichain);
* `two_pow_le_minUniversalSize_sq`:  `2 ^ m ≤ U(2m)²`, i.e. `U(n) ≥ 2^{n/4}`;
* `minUniversalSize_two`          :  `U(2) = 3` exactly.

The theorem of the motivating paper says `U(n) ≤ 2^{(1+η)n/2}` for large `n`;
the exponent therefore lies in `[1/4, 1/2]`, and pinning it down is open.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  `U` is a well-defined `ℕ`-valued function (the set of
admissible sizes is nonempty because the Boolean lattice works), squeezed
between `2^{n/4}` and `2^n`, with `U(1) = 1`, `U(2) = 3` and (experimentally)
`U(3) = 5`.

Experiment (Experimenter).  `U(2) = 3` is *proved* here.  `U(3) = 5` was found by
exhaustive machine search over all `219` partial orders on `4` points and all
`4231` partial orders on `5` points (see `ComputationalEvidence.md`); it is
recorded as computational evidence only, not as a theorem, since the kernel
cannot replay a search of that size.

Analysis (Analyst).  Carrying the host on the *synonym* `Pt N` of `Fin N` rather
than on `Fin N` itself is essential: `Fin N` already carries its own order, and
a transported order must not be silently overwritten by it.  This is the formal
counterpart of the informal phrase "a poset on `N` points".

Critique (Critic).  `minUniversalSize` is a genuine `sInf` over a nonempty set of
naturals, so all four theorems are statements about an attained minimum, not
about a vacuous infimum: nonemptiness is supplied by
`isUniversalPosetOfSize_two_pow`.
-/

open UniversalPosets


instance (N : ℕ) : DecidableEq (Pt N) := inferInstanceAs (DecidableEq (Fin N))













open UniversalPosets in
theorem solution{U : Type} [PartialOrder U] [Fintype U] {N n : ℕ}
    (hcard : Fintype.card U = N) (h : IsUniversalHost U (Fin n)) :
    IsUniversalPosetOfSize N n := by
  classical
  let e : U ≃ Pt N := (Fintype.equivFin U).trans (finCongr hcard)
  refine ⟨fun a b => e.symm a ≤ e.symm b, ?_, ?_⟩
  · exact
      haveI : Std.Refl (fun a b : Pt N => e.symm a ≤ e.symm b) := ⟨fun _ => le_refl _⟩
      haveI : IsTrans (Pt N) (fun a b : Pt N => e.symm a ≤ e.symm b) :=
        ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
      haveI : IsPreorder (Pt N) (fun a b : Pt N => e.symm a ≤ e.symm b) := ⟨⟩
      haveI : Std.Antisymm (fun a b : Pt N => e.symm a ≤ e.symm b) :=
        ⟨fun _ _ h1 h2 => e.symm.injective (le_antisymm h1 h2)⟩
      ⟨⟩
  · intro r hr
    obtain ⟨f, hf⟩ := h r hr
    exact ⟨fun x => e (f x), fun x y => by simpa using hf x y⟩
