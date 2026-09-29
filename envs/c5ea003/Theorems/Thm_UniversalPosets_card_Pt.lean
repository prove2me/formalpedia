-- Prove2me | Theorems.Thm_UniversalPosets_card_Pt
-- name    : UniversalPosets.card_Pt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:04:28.308454+00:00
-- url     : https://prove2.me/theorems/9a4325cb-7d92-46fc-9279-7d1698ce4c33
-- title:
--   Card Pt
-- statement:
--   Formal statement of `UniversalPosets.card_Pt` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem UniversalPosets.card_Pt(N : ℕ) : Fintype.card (Pt N) = N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/UniversalPosets/MinSize.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/UniversalPosets/MinSize.lean#L52

-- Thm stub generated from Cryptography/UniversalPosets/MinSize.lean
import Mathlib
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

@[simp]

theorem UniversalPosets.card_Pt(N : ℕ) : Fintype.card (Pt N) = N := by sorry
