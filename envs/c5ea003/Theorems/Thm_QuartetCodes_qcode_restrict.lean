-- Prove2me | Theorems.Thm_QuartetCodes_qcode_restrict
-- name    : QuartetCodes.qcode_restrict
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:27:41.968666+00:00
-- url     : https://prove2.me/theorems/4edeb116-a4dc-47c0-99c0-2e1b1a549772
-- title:
--   Restriction principle.
-- statement:
--   **Restriction principle.**  Reading a leaf order on `n` leaves along an injective map from
--   `Fin m` produces a leaf order on `m` leaves with the same quartet letters.
--
--   ```lean
--   theorem QuartetCodes.qcode_restrict(π : Equiv.Perm (Fin n)) (f : Fin m → Fin n)
--       (hf : Function.Injective f) :
--       ∃ σ : Equiv.Perm (Fin m), ∀ a b c d : Fin m,
--         qcode π (f a) (f b) (f c) (f d) = qcode σ a b c d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/QuartetCodesSharpPair.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/QuartetCodesSharpPair.lean#L120

-- Thm stub generated from Combinatorics/QuartetCodesSharpPair.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesSharpPair

/-!
# The two-tree quartet threshold is exactly six leaves

`Combinatorics.QuartetCodesUpperBound` shows by Erdős–Szekeres that any two caterpillars on ten
leaves share a quartet, while `QuartetCodes.not_isAgreementThreshold_five_two` exhibits two
caterpillars on five leaves sharing none.  Here the upper end is pushed down to the truth: **six**
leaves already force a common quartet, so the two-tree threshold is exactly `6`.

The proof is the coding-theoretic restriction principle in action.  A quartet letter depends only on
the *relative order* of the four leaves, so restricting a leaf order to any six leaves produces a
genuine six-leaf codeword (`qcode_restrict`), and a six-leaf statement transfers to every larger
leaf set.  The six-leaf statement itself is reduced by the group action
`(π, ρ) ↦ (1, ρ π⁻¹)` to a single quantifier over `Sym(6)` and then decided by the kernel.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Exhaustive computation says that all `720²` pairs of six-leaf caterpillars share a quartet, i.e.
`h(2) = 6`; the Erdős–Szekeres value `10` is an artefact of the proof method.

## Experiment (Experimenter)
Deciding `∀ π ρ : Sym(6), ∃ quartet` directly is `518400` pairs and is out of kernel reach.  Using
the right translation action of `Sym(6)` on pairs, the statement collapses to `720` cases
(`six_leaf_core`), which the kernel checks in about two minutes.  The transfer to `n ≥ 6` leaves
needs the rank permutation of an injective map (`rankPerm`) and the order-invariance of the ternary
letter (`code3_congr`).

## Analysis (Analyst)
The gain (from `10` down to `6`) comes entirely from *not* using Erdős–Szekeres: the quartet letter
is an order invariant, so a purely local six-leaf obstruction suffices.  The same mechanism should
sharpen the `k`-tree bound `3^{2^k}` if the corresponding finite statement can be decided for the
relevant window size.

## Critique (Critic)
`code3_congr` is stated with all twelve order comparisons, so it does not silently assume the four
leaves are distinct; `rankPerm` is built from an explicit rank function with a proved injectivity,
so the statement uses no choice beyond what `Equiv.ofBijective` needs.  The final theorem quantifies
over *all* pairs of leaf orders on *all* `n ≥ 6`, and the exhibited quartet is genuinely made of
four distinct leaves.
-/

open Finset

open QuartetCodes


variable {m n : ℕ}

theorem QuartetCodes.qcode_restrict(π : Equiv.Perm (Fin n)) (f : Fin m → Fin n)
    (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin m), ∀ a b c d : Fin m,
      qcode π (f a) (f b) (f c) (f d) = qcode σ a b c d := by sorry
