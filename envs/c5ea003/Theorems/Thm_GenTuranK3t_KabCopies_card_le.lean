-- Prove2me | Theorems.Thm_GenTuranK3t_KabCopies_card_le
-- name    : GenTuranK3t.KabCopies_card_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:48:25.231352+00:00
-- url     : https://prove2.me/theorems/1e021e03-c63e-485a-aaf7-94e8259436a7
-- title:
--   Main upper bound.
-- statement:
--   **Main upper bound.** In any graph satisfying the common-neighborhood bound (i.e.
--   `K_{3,t}`-free), the number of copies of `K_{a,b}` with `3 ≤ a` and `3 ≤ b` is at most
--   `C(n,3) · C(t-1,b) · C(t-1,a-3)`.
--
--   ```lean
--   theorem GenTuranK3t.KabCopies_card_le(G : SimpleGraph V) [DecidableRel G.Adj] {a b t : ℕ}
--       (ha : 3 ≤ a) (hb : 3 ≤ b) (hcn : CNbound G t) :
--       (KabCopies G a b).card
--         ≤ (Fintype.card V).choose 3 * ((t - 1).choose b * (t - 1).choose (a - 3)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GenTuranAsymptoticBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GenTuranAsymptoticBridge.lean#L203

-- Thm stub generated from Bridges/GenTuranAsymptoticBridge.lean
import Mathlib
import Definitions.Def_Bridges_GenTuranAsymptoticBridge
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge: Generalized Turán counting (extremal combinatorics) ↔ Landau asymptotics (analysis)

The generalized Turán problem asks for the maximum number of copies of a fixed graph `H`
inside an `n`-vertex host graph that avoids a forbidden subgraph `F`.  For `H = K_{a,b}` and
`F = K_{3,b+1}` (with `3 ≤ a ≤ b`) the maximum is `Θ(n^3)`; the *upper* half of this statement
is a Kővári–Sós–Turán-style double count, reproduced here self-containedly as
`KabCopies_cubic_of_K3tFree`.

This file is a **connector**: it re-expresses that purely combinatorial cardinality bound as a
statement in the language of *asymptotic analysis*, using Mathlib's `Asymptotics.IsBigO` and
`Filter.Tendsto`.  Concretely, for any sequence `G : ∀ n, SimpleGraph (Fin n)` of
`K_{3,b+1}`-free graphs:

* `genTuran_KabCopies_isBigO` : the count `n ↦ #{copies of K_{a,b} in Gₙ}` is `O(n^3)` in the
  Landau sense (`=O[atTop]`).  The Landau constant is the *combinatorial* constant
  `C(b, a-3)` — the bridge carries the extremal constant into the analytic statement.
* `genTuran_density_tendsto_zero` : the normalized "copy density" `#copies / n^{a+b}` tends to
  `0`.  Since a labelled `K_{a,b}` lives on `a+b ≥ 6` vertices while the count is only cubic,
  the fraction of vertex placements realizing a copy vanishes — a probabilistic/analytic
  reading of the same extremal fact.

The two named results genuinely *consume* the combinatorial theorem `KabCopies_cubic_of_K3tFree`
as a black box, so the file is a faithful bridge rather than a restatement.

## Catalog connections
* `Generalized Turán number` / `Alon–Shikhelman`: `KabCopies` is the counting object.
* `Kővári–Sós–Turán theorem`: `cnbhd_card_le` is the common-neighborhood cap that drives the
  double count.
* `Complete bipartite graphs`: both the counted graph `K_{a,b}` and the forbidden `K_{3,b+1}`.
-/

open Finset

open GenTuranK3t

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The combinatorial core (self-contained upper bound)

The material in this section reproduces the elementary `O(n^3)` upper bound for
`ex(n, K_{a,b}, K_{3,t})`, so that the asymptotic bridge below is self-contained. -/

theorem GenTuranK3t.KabCopies_card_le(G : SimpleGraph V) [DecidableRel G.Adj] {a b t : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hcn : CNbound G t) :
    (KabCopies G a b).card
      ≤ (Fintype.card V).choose 3 * ((t - 1).choose b * (t - 1).choose (a - 3)) := by sorry
