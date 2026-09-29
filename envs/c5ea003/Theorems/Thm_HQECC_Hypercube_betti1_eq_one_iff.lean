-- Prove2me | Theorems.Thm_HQECC_Hypercube_betti1_eq_one_iff
-- name    : HQECC.Hypercube.betti1_eq_one_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:40:17.509271+00:00
-- url     : https://prove2.me/theorems/7fbc11e7-2037-49b4-867a-6a244f83758a
-- title:
--   The "one qubit" law holds only at `n = 2`.
-- statement:
--   **The "one qubit" law holds only at `n = 2`.**  For every `n â¥ 1`,
--   `Î²â(Qâ) = 1` if and only if `n = 2`.
--
--   ```lean
--   theorem HQECC.Hypercube.betti1_eq_one_iff(n : ℕ) (hn : 1 ≤ n) : betti1 n = 1 ↔ n = 2 := by sorry
--
--   /-! ## The three test cases requested by the mission -/
--
--
--
--
--
--   /-! ## Bridge to the homological code -/
--
--   open CSSComplex
--
--
--
--   /-! ## Examples and sanity checks -/
--
--
--   #check @hypercube_HQECC_count
--   #check @Hypercube.betti1_closed
--   #eval (List.range 9).map (fun n => (n, Hypercube.betti1 n))   -- [.., (4,17), (6,129), (8,769)]
--
--   /-- The predicted logical-qubit counts for the mission's test cases. -/
--   example : Hypercube.betti1 4 = 17 ∧ Hypercube.betti1 6 = 129 ∧ Hypercube.betti1 8 = 769 :=
--     ⟨Hypercube.betti1_four, Hypercube.betti1_six, Hypercube.betti1_eight⟩
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/HQECC/HypercubeCounterexample.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/HQECC/HypercubeCounterexample.lean#L82

-- Thm stub generated from Shared/HQECC/HypercubeCounterexample.lean
import Mathlib
import Definitions.Def_Shared_HQECC_CSSHomology
import Definitions.Def_Shared_HQECC_HypercubeCounterexample

open HQECC

/-!
# The homological code of the hypercube, and the failure of the "1 qubit" law

The homological quantum error correcting code `HQECC(G)` of a graph `G` (a
one–dimensional simplicial complex) uses the boundary map `∂ : 𝔽₂^E → 𝔽₂^V` as
its only differential (there are no 2–cells, so `d₂ = 0`).  By the graph count
`CSSComplex.graph_numLogical_add`, the number of logical qubits equals the
**circuit rank** (first Betti number)

  `k = β₁(G) = E − V + β₀`,

where `E, V` are the edge and vertex counts and `β₀` the number of connected
components.  For a *connected* graph `β₀ = 1`, so `k = E − V + 1`.

We apply this to the `n`-dimensional hypercube graph `Qₙ`, which has
`V = 2ⁿ` vertices and `E = n·2ⁿ⁻¹` edges and is connected.  Hence

  `β₁(Qₙ) = n·2ⁿ⁻¹ − 2ⁿ + 1 = 2ⁿ⁻¹·(n − 2) + 1`.

A widely quoted conjecture asserts that `HQECC(Qₙ)` encodes a **single** logical
qubit for all `n`.  Our computation shows this is *false* for every `n ≥ 3`: the
code encodes `2ⁿ⁻¹·(n − 2) + 1` logical qubits, e.g. `17` for `Q₄`, `129` for
`Q₆`, `769` for `Q₈`.  The "one qubit" law holds **only** in the boundary case
`n = 2`, where `Q₂` is the 4-cycle.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  Reading the mission literally, `HQECC(Qₙ)` should
encode `1` logical qubit with distance `2^{n/2}`.  The graph `Qₙ` is a genuine
1-complex, so its first homology is the *cycle space*, whose dimension is the
circuit rank `E − V + 1`, not `1`.  We therefore predict the conjecture is FALSE
for large `n` and pin down the exact (topological) invariant.

EXPERIMENT (Experimenter).  We compute `E, V` for `Qₙ`, derive the closed form
`β₁(Qₙ) = 2ⁿ⁻¹(n−2)+1`, and prove `β₁(Qₙ) = 1 ↔ n = 2` together with
`β₁(Qₙ) ≥ 5` for `n ≥ 3`.  The bridge theorem `hypercube_HQECC_count` transports
this to the homological code via `CSSComplex.graph_numLogical_add` from the
catalog file `CSSHomology.lean`.

ANALYSIS (Analyst).  The conjecture confuses the hypercube *graph* (a 1-complex,
first Betti number `2ⁿ⁻¹(n−2)+1`) with the hypercube *cell complex* / torus-like
surface (whose middle homology can be small).  The correct statement is a clean
topological invariant.  The "1 qubit" claim survives *only* at `n = 2`.

CRITIQUE (Critic).  All arithmetic identities are proved by `ring`/`omega` after
recording `2ⁿ = 2·2ⁿ⁻¹`, none by `decide` alone on the general statement; the
three numerical instances `Q₄, Q₆, Q₈` are genuine evaluations.  The bridge
theorem uses the catalog homology count, so the result is not self-referential.
-/

open Hypercube




/-! ## Closed form and the boundary case -/

theorem HQECC.Hypercube.betti1_eq_one_iff(n : ℕ) (hn : 1 ≤ n) : betti1 n = 1 ↔ n = 2 := by sorry
