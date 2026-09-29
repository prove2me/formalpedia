-- Prove2me | Theorems.Thm_Hashimoto_trace_hashimoto_pow
-- name    : Hashimoto.trace_hashimoto_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:34:26.833001+00:00
-- url     : https://prove2.me/theorems/a2242828-4ffb-4b7c-8790-772a7b4bba59
-- title:
--   Main theorem.
-- statement:
--   **Main theorem.** The trace of the `n`-th power of the Hashimoto matrix is the number
--   of rooted closed non-backtracking walks of length `n`.
--
--   ```lean
--   theorem Hashimoto.trace_hashimoto_pow(n : ℕ) :
--       (hashimoto G ^ n).trace = (closedNBWalks G n).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/NonBacktracking/HashimotoTrace.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/NonBacktracking/HashimotoTrace.lean#L110

-- Thm stub generated from Algebra/NonBacktracking/HashimotoTrace.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount

/-!
# `trace (Bⁿ)` counts rooted closed non-backtracking walks of length `n`

Let `G` be a finite simple graph and let `B` be its **Hashimoto (non-backtracking)
matrix**: the `0-1` matrix indexed by the *darts* (oriented edges) of `G` with

`B d d' = 1` iff `d` and `d'` are composable (`d.snd = d'.fst`) and `d'` is not the
reversal of `d`.

The main results of this file are the two forms of the trace formula:

* `Hashimoto.trace_hashimoto_pow` :
  `trace (B ^ n) = #{ rooted closed non-backtracking walks of length n }`,
  where such a walk is a list of `n + 1` darts, consecutive darts composable without
  backtracking, whose first and last dart agree (the root);
* `Hashimoto.trace_hashimoto_pow_eq_card_nbCycles` (for `1 ≤ n`) :
  `trace (B ^ n) = #{ cyclically non-backtracking sequences of n darts }`,
  the classical "rooted closed non-backtracking walk of length `n`" of Ihara-zeta
  theory: `n` darts arranged in a cycle, non-backtracking also across the seam.

Both counts are genuine finite cardinalities (`Finset.card`), and the two counting
sets are proved to be in bijection (`Hashimoto.card_nbCycles`).

We also prove the first structural consequences:

* `Hashimoto.trace_hashimoto_pow_zero` : `trace (B ^ 0) = #darts = ∑ v, deg v`;
* `Hashimoto.trace_hashimoto` and `Hashimoto.trace_hashimoto_sq` : `trace B = trace (B²) = 0`
  (a graph has no closed non-backtracking walks of length `1` or `2`);
* `Hashimoto.rowSum_hashimoto` : the `d`-th row of `B` sums to `deg (d.snd) - 1`;
* `Hashimoto.trace_hashimoto_pow_le_of_regular` : for a `(q+1)`-regular graph,
  `trace (B ^ n) ≤ (#darts) * qⁿ`, i.e. the exponential growth rate of the number of
  closed non-backtracking walks is at most `q` (the Ihara/Alon–Boppana regime).

The underlying general digraph walk-counting machinery lives in
`Algebra.NonBacktracking.RelWalkCount`.
-/

open Finset RelWalkCount SimpleGraph

open Hashimoto

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


/-! ## The non-backtracking relation on darts -/



variable {G}




variable (G)

/-! ## The Hashimoto matrix -/



/-! ## Rooted closed non-backtracking walks -/

theorem Hashimoto.trace_hashimoto_pow(n : ℕ) :
    (hashimoto G ^ n).trace = (closedNBWalks G n).card := by sorry
