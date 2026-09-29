-- Prove2me | Theorems.Thm_AdjSum_cycExt_surjective_on_periodic
-- name    : AdjSum.cycExt_surjective_on_periodic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:12:22.296618+00:00
-- url     : https://prove2.me/theorems/8c162c4b-3693-4f93-9136-49141058e9d0
-- title:
--   The image of the periodic extension is exactly the set of `(e+1)`-periodic words.
-- statement:
--   The image of the periodic extension is exactly the set of `(e+1)`-periodic words.
--
--   ```lean
--   theorem AdjSum.cycExt_surjective_on_periodic{s e q : ℕ} (h : (e + 1) ∣ (q + 1)) (x : CycPt s q)
--       (hx : (rot s q)^[e + 1] x = x) : ∃ y : CycPt s e, cycExt h y = x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AdjacentSumPolytopes/GaussCongruence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AdjacentSumPolytopes/GaussCongruence.lean#L170

-- Thm stub generated from Applications/AdjacentSumPolytopes/GaussCongruence.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_GaussCongruence
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace

/-!
# The full Gauss congruence for the adjacent-sum transfer matrix

`Applications.AdjacentSumPolytopes.Necklace` proved the Gauss congruence
`p ∣ tr(Mᵖ) − tr(M)` for *prime* lengths, using the `p`-group fixed point formula, and
left the general case as a conjecture.  Here we settle it:

`n ∣ ∑_{d ∣ n} μ(n/d) · tr(Mⁿ)`   for every `n ≥ 1`,

where `M = adjMat s` is the adjacent-sum transfer matrix.  Equivalently the *primitive*
cyclic counts `primCyc s n` — the Möbius transform of the trace sequence — count the
aperiodic cyclic adjacent-sum words, hence are divisible by their length.

The proof is the necklace argument, made precise:

* `cycExt` extends a cyclic word of length `e + 1` periodically to a cyclic word of
  length `q + 1` whenever `(e+1) ∣ (q+1)`; it is injective, rotation-equivariant, and its
  image is exactly the set of `(e+1)`-periodic words (`cycExt_surjective_on_periodic`);
* therefore the number of length-`(q+1)` words of *exact* period `d` equals the number of
  *aperiodic* words of length `d` (`card_minimalPeriod_eq_aper`);
* the abstract orbit-peeling lemma of `Applications.AdjacentSumPolytopes.Periodicity`
  gives `d ∣ aperCyc s d`, and Möbius inversion identifies `aperCyc s n = primCyc s n`.

-- !-- Lab Notes -- !--
* **Hypothesis.** `primCyc s n` counts aperiodic cyclic adjacent-sum words of length `n`,
  hence `n ∣ primCyc s n` for all `n ≥ 1`, not only for `n` prime.
* **Experiment.** `s = 2`, trace sequence `tr(Mⁿ) = 2, 6, 11, 26, 57, 129, 289` for
  `n = 1..7`.  Möbius transforms: `primCyc 1 = 2`, `primCyc 2 = 6 - 2 = 4`,
  `primCyc 3 = 11 - 2 = 9`, `primCyc 4 = 26 - 6 = 20`, `primCyc 6 = 129 - 11 - 6 + 2 = 114`.
  Divisibility: `1∣2`, `2∣4`, `3∣9`, `4∣20`, `6∣114 = 6·19`.  The composite cases `4` and
  `6` are exactly the ones the prime-only argument could not reach.
* **Analysis.** The obstruction in the previous cycle was that the `p`-group fixed-point
  theorem only sees prime lengths.  Replacing it by the exact-period decomposition
  removes the arithmetic hypothesis entirely: the only input is that rotation is an
  injective map with `rot^[n] = id`.
* **Critique.** The argument nowhere assumes the alphabet nonempty or the constraint
  nontrivial; the degenerate readings are still true statements, and for `s ≥ 0` the
  counts are positive (the all-zero word is always admissible), so the congruence is not
  vacuous.
-/

open AdjSum

open Finset Function Matrix






/-! ## Iterates of the rotation -/





/-! ## Periodic extension of cyclic words -/

theorem AdjSum.cycExt_surjective_on_periodic{s e q : ℕ} (h : (e + 1) ∣ (q + 1)) (x : CycPt s q)
    (hx : (rot s q)^[e + 1] x = x) : ∃ y : CycPt s e, cycExt h y = x := by sorry
