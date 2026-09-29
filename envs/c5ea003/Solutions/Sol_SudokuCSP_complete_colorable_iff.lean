-- Prove2me | solution 1 for SudokuCSP.complete_colorable_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:27:36.280802+00:00
-- url     : https://prove2.me/submissions/05356b5e-2ca0-4585-abda-ffeff10e4d19

-- Sol generated from Applications/SudokuConstraintThreshold.lean
import Mathlib
import Definitions.Def_Applications_SudokuConstraintThreshold

/-!
# The Constraint-Satisfaction Threshold of Sudoku: A Sharp Phase Transition

Sudoku is the archetypal *constraint-satisfaction problem* (CSP).  Every row,
column and box imposes a single combinatorial demand — an **AllDifferent**
constraint: a block of `m` cells must receive pairwise distinct symbols drawn
from an alphabet of size `k`.  This file isolates the AllDifferent atom, proves
that its satisfiability undergoes a **sharp phase transition** as the number of
cells crosses the alphabet size, and threads that transition through three
distinct mathematical languages:

* **order theory** — the satisfiable region is exactly the down-set `[0, k]`, so
  the transition is a single jump at the critical cell count `k + 1`, never a
  gradual slope (`alldiff_sat_iff_le`, `sat_set_eq_Iic`, `critCells_unique`);
* **enumerative combinatorics / statistical mechanics** — the "partition
  function" counting proper assignments is the falling factorial
  `k^{\underline m}`; it is strictly positive in the satisfiable phase and
  collapses to `0` exactly at criticality (`numProper_pos_iff_sat`,
  `numProper_crit`, `numProper_over`);
* **graph theory** — an AllDifferent block is a complete graph, so the CSP is a
  proper colouring problem and satisfiability equals `k`-colourability of `Kₘ`
  (`complete_colorable_iff`, `complete_colorable_iff_le`).

For an order-`n` Sudoku the grid is `n² × n²` and *every* line contains exactly
`n²` cells drawn from `n²` symbols: the puzzle sits precisely **at criticality**
(`sudoku_row_sat`, `sudoku_row_over_unsat`), which is the structural reason
Sudoku is a hard, critically-constrained problem.  Finally we exhibit an
*explicit* simultaneous solution of the row-and-column CSP — the cyclic Latin
square `L(i,j) = i + j` over `ℤ/Nℤ` — turning the abstract existence statement
into a group-theoretic construction (`exists_latin_square`).

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  Sudoku's difficulty is not accidental: the
  AllDifferent atom that generates every constraint should exhibit a *sharp*
  satisfiability threshold, and the `n² × n²` grid should sit exactly on it.  A
  bolder cross-domain claim: the same threshold is visible simultaneously as an
  order-theoretic down-set, a vanishing enumerative partition function, and a
  graph-colourability boundary.
* **Experiment (Experimenter).**  Modelled the AllDifferent atom by
  `AllDiffSAT m k := ∃ f : Fin m → Fin k, Injective f` and proved the pigeonhole
  equivalence `AllDiffSAT m k ↔ m ≤ k`.  From this single equivalence we derived
  the down-set description, the sharp critical value `k + 1`, its uniqueness, the
  partition-function collapse via `Nat.descFactorial`, and the graph-colouring
  bridge through `SimpleGraph.Coloring`.  The Latin-square witness came from
  bijectivity of translation in the finite group `ℤ/Nℤ`.
* **Analysis (Analyst).**  "True and structural."  Every result funnels through
  one pigeonhole equivalence, which is why the three languages agree: they are
  three faces of `m ≤ k`.  The critical case `m = k` lands on the *satisfiable*
  side (the boundary is closed below), matching the fact that a full Sudoku
  solution exists; the very next cell (`m = k + 1`) is unconditionally
  infeasible.
* **Critique (Critic).**  Corner cases: `m = 0` is vacuously satisfiable for
  every alphabet, and `k = 0` forces immediate infeasibility for any nonempty
  block — both are genuine (degenerate) instances of the transition, not false
  claims.  The density statement is guarded by `0 < k` to avoid division by
  zero.  The Latin square solves rows and columns but *not* boxes, so it is
  honestly labelled a solution of the CSP *relaxation*, not of full Sudoku.
* **Synthesis (PI).**  The satisfiability of a constraint-satisfaction puzzle is
  governed by a single sharp threshold in the balance between demands and
  resources; Sudoku is engineered to sit exactly at that threshold, and the
  threshold is simultaneously an order-theoretic, enumerative, and
  chromatic phenomenon.
-/

open Function SimpleGraph

open SudokuCSP

/-! ## 1. The AllDifferent atom and its pigeonhole equivalence -/






/-! ## 2. The sharp phase transition -/






/-! ## 3. The partition function (enumerative / statistical-mechanics view) -/







/-! ## 4. Density and the critical density `1` -/



/-! ## 5. Specialisation to Sudoku: the grid sits at criticality -/




/-! ## 6. Graph-theoretic bridge: AllDifferent = colouring a complete graph -/



/-! ## 7. An explicit simultaneous solution: the cyclic Latin square -/



/-! ## 8. Worked instances (PEGB: examples, boundary, generalization checks) -/

-- The classic `9 × 9` Sudoku is critically constrained (order `n = 3`).
-- example : AllDiffSAT 9 9 := sudoku_row_sat 3
-- example : ¬ AllDiffSAT 10 9 := by rw [alldiff_unsat_iff_gt]; norm_num

-- The number of ways to fill one full `9`-cell line is `9! = 362880`.
example : numProper 9 9 = 362880 := by decide

-- #check @alldiff_sat_iff_le
-- #check @complete_colorable_iff_le
-- #check @exists_latin_square
-- #eval numProper 9 9          -- 362880
-- #eval numProper 10 9         -- 0  (supercritical collapse)
-- #eval numProper 4 4          -- 24 = 4!  (order-2 Sudoku line)


open SudokuCSP in
theorem solution(m k : ℕ) :
    (⊤ : SimpleGraph (Fin m)).Colorable k ↔ AllDiffSAT m k := by
  constructor
  · rintro ⟨C⟩
    refine ⟨C, ?_⟩
    intro a b hab
    by_contra hne
    have : (⊤ : SimpleGraph (Fin m)).Adj a b := by
      simpa [SimpleGraph.top_adj] using hne
    exact (C.valid this) hab
  · rintro ⟨f, hf⟩
    exact ⟨SimpleGraph.Coloring.mk f
      (by intro a b hab; simp only [SimpleGraph.top_adj] at hab; exact fun h => hab (hf h))⟩
