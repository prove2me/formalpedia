-- Prove2me | Definitions.Def_Cryptography_UniversalPosets_StrictMono
-- name    : Cryptography_UniversalPosets_StrictMono
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:28:22.238085+00:00
-- url     : https://prove2.me/theorems/ec7c9c5f-167c-45b6-9219-d7cf79112f65
-- title:
--   Aether Catalog definitions — Cryptography_UniversalPosets_StrictMono
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.UniversalPosets.StrictMono`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/UniversalPosets/StrictMono.lean by skeleton subtraction
import Mathlib

/-!
# `U` is strictly increasing

`ExactSmall.lean` showed that `U` is monotone (adding an isolated point to a
poset).  Here the monotonicity is upgraded to a *strict* one:

`U(n) < U(n+1)` for every `n`.

The mechanism is a genuine structural one, not a counting one.  Let `H` be a
host containing every `(n+1)`-element poset, and let `m` be a maximal point of
`H`.  Given an `n`-element poset `r`, add to `r` a new element `⊤` above
everything (`extendTopRel`).  In any induced copy of `r + ⊤` inside `H` the
image of `⊤` is strictly above the images of the other `n` points, so *none* of
those `n` points can be the maximal point `m`.  Hence `H \ {m}`, which has one
point fewer, is already universal for the `n`-element posets.

Consequences: `U` is strictly monotone, and therefore injective; and any exact
value propagates, e.g. `U(n) ≥ n + 2` for `n ≥ 2` follows from `U(2) = 3`
(and is subsumed by the sharper `2n - 1` bound of `ExactSmall.lean`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  Conjecture C4 of the previous cycle asked whether
`U` is strictly increasing.  The known values `1, 3, 5` are consistent with it,
and the natural mechanism is that a *top* point of the added element cannot be
reused as a maximal point of the host.

Experiment (Experimenter).  The mechanism was tested against the `300` five-point
hosts universal for three-element posets: deleting a maximal point of any one of
them leaves a four-point poset which is universal for the two-element posets
(`U(2) = 3 ≤ 4`), as the argument predicts.

Analysis (Analyst).  The argument only needs the *existence* of a maximal point,
so it works in any finite host, and it needs the extension by a global top,
which is the smallest extension whose embedding is forced away from the maximum.
The same argument with a minimal point and a global bottom gives the same bound.

Critique (Critic).  Strict monotonicity gives only `U(n) ≥ U(3) + n - 3`, weaker
than `2n - 1`; its value is qualitative (`U` is injective, no plateaux), and it
closes the "strictly increasing" half of conjecture C4 of the previous cycle.
The recursive half of C4 (`U(n+1) ≤ 2U(n) + 1`) remains open and is restated in
`FUTURE_DIRECTIONS.md`.
-/

namespace UniversalPosets

open Function

/-- Adjoining a new greatest element to an `n`-element order. -/
private def extendTopRel {n : ℕ} (r : Fin n → Fin n → Prop) :
    Fin (n + 1) → Fin (n + 1) → Prop :=
  fun x y => y = Fin.last n ∨ ∃ hx : (x : ℕ) < n, ∃ hy : (y : ℕ) < n, r ⟨x, hx⟩ ⟨y, hy⟩






end UniversalPosets


