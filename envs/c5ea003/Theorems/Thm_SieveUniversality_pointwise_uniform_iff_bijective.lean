-- Prove2me | Theorems.Thm_SieveUniversality_pointwise_uniform_iff_bijective
-- name    : SieveUniversality.pointwise_uniform_iff_bijective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:51:43.500395+00:00
-- url     : https://prove2.me/theorems/61df9a8f-4360-4710-9cf5-992be1e94900
-- title:
--   Pointwise random-equivalence is exactly bijectivity.
-- statement:
--   **Pointwise random-equivalence is exactly bijectivity.**  A sieve map hits
--   every target exactly once per period iff it is a bijection of residues; any
--   non-bijective sieve map (such as squaring) necessarily has a nontrivial
--   `0`/`â¥2` dichotomy, which is what a quadratic-character constraint looks like.
--
--   ```lean
--   theorem SieveUniversality.pointwise_uniform_iff_bijective(f : α → β) :
--       (∀ b, hitCount f b = 1) ↔ Function.Bijective f := by sorry
--   /-! ## The quadratic sieve instance -/
--
--   variable {p : ℕ} [Fact p.Prime]
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/SievePolynomialUniversality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/SievePolynomialUniversality.lean#L52

-- Thm stub generated from Shared/SievePolynomialUniversality.lean
import Mathlib
import Definitions.Def_Shared_QSRelationPoolRandom
import Definitions.Def_Shared_SievePolynomialUniversality

/-!
# Universality of on-average random-equivalence for sieve polynomials

The exact cancellation of `Catalog.Shared.QSRelationPoolRandom` invites the
question: is the quadratic sieve special?  It is not.  This file isolates the
combinatorial skeleton of the phenomenon and shows it is *universal*: for **any**
sieve map `f` on residues (any polynomial, any degree, any modulus), the number
of `x` per period hitting a given target residue averages to exactly
`|domain| / |targets|`, the random-model value.  Averaged over the target, no
sieve polynomial can be better or worse than random.

What the individual polynomial controls is only the *distribution* of that hit
count across targets, and the file characterises exactly when the pool is
random-equivalent target-by-target rather than merely on average:

* `sum_fiber_card` — the averaging identity (universality).
* `pointwise_uniform_iff_bijective` — pointwise random-equivalence holds iff the
  sieve map is a bijection of residues.
* `sq_not_pointwise_uniform` — for `x ↦ x^2` mod an odd prime it fails: the
  hit count is the `2`/`0` dichotomy, never the constant `1`.
* `qs_average_hits_eq_random` — but on average over the modulus residue the
  quadratic sieve hits exactly once per period, like a random sequence.

The moral for the experiment: any measured deviation of the `x^2 - N` pool from
the random control must come from the *interaction across primes* for one fixed
`N`, never from the one-prime statistics, which are pinned by these identities.
-/

open SieveUniversality

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]



omit [Fintype β] in

theorem SieveUniversality.pointwise_uniform_iff_bijective(f : α → β) :
    (∀ b, hitCount f b = 1) ↔ Function.Bijective f := by sorry
