-- Prove2me | Definitions.Def_Cryptography_UniversalPosets_MinSize
-- name    : Cryptography_UniversalPosets_MinSize
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:26:11.972992+00:00
-- url     : https://prove2.me/theorems/dd7d4af0-5115-48ad-8453-cf72b5d9c808
-- title:
--   Aether Catalog definitions — Cryptography_UniversalPosets_MinSize
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.UniversalPosets.MinSize`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/UniversalPosets/MinSize.lean by skeleton subtraction
import Mathlib

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

namespace UniversalPosets

/-- An `N`-point carrier with **no** ambient order (a synonym of `Fin N`). -/
def Pt (N : ℕ) : Type := Fin N

instance (N : ℕ) : Fintype (Pt N) := inferInstanceAs (Fintype (Fin N))
instance (N : ℕ) : DecidableEq (Pt N) := inferInstanceAs (DecidableEq (Fin N))


/--
`IsUniversalPosetOfSize N n` : there is a partial order on `N` points containing
every partial order on `n` points as an induced subposet.
-/
def IsUniversalPosetOfSize (N n : ℕ) : Prop :=
  ∃ H : Pt N → Pt N → Prop, IsPartialOrder (Pt N) H ∧
    ∀ r : Fin n → Fin n → Prop, IsPartialOrder (Fin n) r →
      ∃ f : Fin n → Pt N, ∀ x y, H (f x) (f y) ↔ r x y

/-- The size of a smallest universal poset for the `n`-element posets. -/
noncomputable def minUniversalSize (n : ℕ) : ℕ :=
  sInf {N | IsUniversalPosetOfSize N n}









end UniversalPosets


