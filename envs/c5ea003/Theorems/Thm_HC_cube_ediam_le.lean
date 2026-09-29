-- Prove2me | Theorems.Thm_HC_cube_ediam_le
-- name    : HC.cube_ediam_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:43:15.921729+00:00
-- url     : https://prove2.me/theorems/d0c99456-d78e-437c-9784-0ef1067ab4ea
-- title:
--   A concrete chord‑swap‑type reconfiguration graph meets the bound.
-- statement:
--   **A concrete chord‑swap‑type reconfiguration graph meets the bound.**  The
--   `d`‑dimensional bit–swap graph has diameter at most `2d`: Hamming weight is a
--   monovariant potential descending to the all‑zero hub one coordinate at a time,
--   so the general descent theorem applies.  This is a faithful, non‑vacuous witness
--   that the potential‑descent architecture governs genuine reconfiguration graphs,
--   and that the diameter is linear in the number of local moves available.
--
--   ```lean
--   theorem HC.cube_ediam_le: (cube d).ediam ≤ (2 * d : ℕ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/NumberTheory/NeuralCoding/ChordSwapDiameterDescent.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/NumberTheory/NeuralCoding/ChordSwapDiameterDescent.lean#L178

-- Thm stub generated from Speculative/NumberTheory/NeuralCoding/ChordSwapDiameterDescent.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_NeuralCoding_ChordSwapDiameterDescent

/-!
# Descent potentials and diameter bounds for chord–swap reconfiguration graphs

A *chord diagram* of size `n` is a perfect matching of `2n` points on a circle;
its *genus* `g` measures the topological complexity of the surface obtained by
thickening the chords.  The **chord–swap graph** has these diagrams as vertices,
with an edge whenever two diagrams differ by a single *swap* (reconnecting the
four endpoints of two chords).  A central quantitative question about this graph
— studied in connection with polygonal side–matchings and the mixing of the
associated Markov chain — is how large its diameter can be on the locus of fixed
genus `g` and size `n`.  It is known that this diameter is `O(n + g²)` for
`n > 2g`; the sharp form of the constant is conjectural.

Every known upper bound on such reconfiguration diameters follows the same
architecture: one exhibits a *canonical* diagram `c` (a hub) together with a
non‑negative **potential** `φ` that strictly decreases along some swap out of
every non‑canonical diagram.  Iterating the descent drives any diagram to the
hub in at most `φ` steps, and the triangle inequality doubles this into a
diameter bound.  This file isolates that architecture as reusable graph theory
and then instantiates it on a genuine reconfiguration graph — the *bit–swap
graph* (hypercube), whose moves flip a single coordinate exactly as a chord swap
toggles a single crossing.

## Main results

* `edist_hub_le_potential` — **the descent engine.**  If from every vertex other
  than the hub `c` there is an edge along which `φ` strictly decreases, then the
  distance from any vertex `v` to `c` is at most `φ v`.  Equivalently: the
  *eccentricity of the canonical diagram* (the graph radius witnessed by `c`) is
  bounded by the potential.  This is exactly the home of the sharp‑constant
  conjecture: taking `φ v ≤ n + g²` yields radius `≤ n + g²`, the `C = 1` form.

* `ediam_le_two_mul_of_potential` — **the diameter bound.**  A potential bounded
  by `B` forces the whole graph to have diameter at most `2B`.  With
  `B = n + g²` this reproduces the `O(n + g²)` diameter with an explicit
  universal constant `C = 2`.

* `HC.cube_ediam_le` — **a concrete swap graph.**  The `d`‑dimensional bit–swap
  graph, where two `0/1`‑vectors are adjacent iff they differ in exactly one
  coordinate, carries the Hamming‑weight potential, which descends to the
  all‑zero hub one bit at a time.  Hence its diameter is at most `2d`.  This is a
  faithful, non‑vacuous witness that the descent architecture applies to a real
  reconfiguration graph.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  The `O(n+g²)` diameter bound is not special to
  chord diagrams; it is a shadow of a universal *potential‑descent* principle.
  Bold form: for any reconfiguration graph admitting a hub and a monovariant
  potential `φ`, the radius is `≤ max φ` and the diameter is `≤ 2·max φ`, and the
  conjectured sharp constant `C = 1` is really a statement about the *radius*
  (distance to the canonical diagram), which the diameter inflates by a factor 2.
* **Experiment (Experimenter).**  Proved the radius bound by strong induction on
  `φ v` (`Nat.strong_induction_on`): a strictly‑decreasing neighbour `w` gives
  `edist v c ≤ 1 + edist w c ≤ 1 + φ w ≤ φ v`.  The diameter bound follows from
  the (unconditional, `ℕ∞`‑valued) triangle inequality through the hub.  For
  non‑vacuity we built the bit–swap graph and verified the descent hypothesis via
  a single coordinate flip; the potential is Hamming weight, bounded by `d`.
* **Analysis (Analyst).**  The argument is "true and structural".  Working in
  `ℕ∞` with `edist`/`ediam` sidesteps all connectivity bookkeeping: an
  unreachable pair simply has distance `0 ≤ anything`, and `edist_triangle`
  holds unconditionally.  The only arithmetic content is `φ w < φ v ⇒
  1 + φ w ≤ φ v` in `ℕ`.  The bit–swap instantiation shows the hypotheses are
  simultaneously satisfiable, so the bounds are not vacuous.
* **Critique (Critic).**  Is the diameter bound trivial?  No: it fails without the
  descent hypothesis (a graph with an isolated vertex has infinite `ediam` yet a
  bounded potential), so the monovariant condition is load‑bearing.  Is the
  hypercube example a mere restatement?  No: verifying the descent requires an
  explicit witness move (coordinate flip) and the combinatorial fact that
  flipping a set bit drops the weight by one (`weight_update_false_lt`).  No
  theorem here references itself; the three results build up strictly.
* **Synthesis (PI).**  The chord–swap diameter question factors cleanly into
  (i) this universal descent engine and (ii) the diagram‑specific task of
  constructing a swap that lowers a genus‑aware potential by `1` — the latter
  being where the sharp `n + g²` constant must be won.  The `C = 1` conjecture is
  the assertion that the canonical diagram has eccentricity exactly `n + g²`.
-/

open SimpleGraph



open HC

variable {d : ℕ}

theorem HC.cube_ediam_le: (cube d).ediam ≤ (2 * d : ℕ) := by sorry
