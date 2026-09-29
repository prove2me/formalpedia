-- Prove2me | Theorems.Thm_SheafCohomologyRobustness_TorusNerve_rowHol_const
-- name    : SheafCohomologyRobustness.TorusNerve.rowHol_const
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T02:36:41.218183+00:00
-- url     : https://prove2.me/theorems/a602b435-8b48-4896-92c2-e79d2230493a
-- title:
--   RowHol const
-- statement:
--   Formal statement of `SheafCohomologyRobustness.TorusNerve.rowHol_const` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SheafCohomologyRobustness.TorusNerve.rowHol_const{h v : Grid m n → ℝ} (hflat : Flat h v) (b : Fin (n + 1)) :
--       rowHol h b = rowHol h 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/SheafCohomologyRobustness/TorusNerve.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/SheafCohomologyRobustness/TorusNerve.lean#L153

-- Thm stub generated from MachineLearning/SheafCohomologyRobustness/TorusNerve.lean
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_CyclicHolonomy
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_TorusNerve
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# `H¹` of the Discrete Torus Nerve: Two Independent Adversarial Holonomies

A cover of a neural network's weight space by activation regions that is periodic
in **two** parameters (e.g. a two-parameter family of reparametrisations, or a
loop of layers crossed with a loop of input directions) has as nerve the discrete
torus: the `(m+1) × (n+1)` grid graph with wrap-around in both directions.

This file computes its first Čech cohomology exactly.  A `1`-cochain is a pair
`(h, v)` of horizontal and vertical overlap discrepancies; the Čech `2`-cocycle
condition (`Flat`) is the vanishing of the discrepancy around each unit
plaquette.  The results:

* `flat_of_coboundary` — coboundaries are flat (`δ² = 0` for the grid).
* `rowHol_const`, `colHol_const` — for a flat cochain the row holonomy is
  independent of the row and the column holonomy is independent of the column:
  the two holonomies are well-defined invariants.
* `torus_isCoboundary_iff` — a flat cochain is a coboundary **iff both**
  holonomies vanish.  The explicit potential `torusPotential` is built by
  integrating `h` along the base row and then `v` up each column, the
  plaquette condition being exactly what makes this consistent.
* `torusH1EquivProd`, `finrank_torusH1` — hence
  `H¹(torus nerve, ℝ) ≃ₗ[ℝ] ℝ × ℝ` and `dim H¹ = 2`.  A doubly periodic cover
  carries **two** independent adversarial obstruction classes, in exact analogy
  with the first Betti number of the topological torus.

This is a genuine cross-domain statement: a Künneth-type computation of a
discrete cohomology, applied to certified robustness bookkeeping.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer, bold): "the number of independent adversarial
  obstruction classes of a periodic cover equals the first Betti number of the
  nerve; for a doubly periodic cover it is `2`, not `1`."
* Experiment (Experimenter): the potential `P(a) + ∑_{b' < b} v(a, b')` fails
  the horizontal equation unless the plaquette identity is used to convert a
  telescoping sum of `v`-differences into a telescoping sum of `h`-differences;
  this conversion (`horizontal_transport`) is the technical heart, and it is
  where the `2`-cocycle condition earns its keep.
* Analysis (Analyst): the failed naive attempt (integrating `v` along the base
  column and `h` along rows) is not symmetric-equivalent — it needs the *same*
  plaquette identity in the transposed form.  Structural pattern: for a product
  nerve, the potential must be integrated in a fixed order, and flatness is the
  compatibility of the two orders.
* Critique (Critic): both holonomies are genuinely realised
  (`torus_holonomy_surjective` exhibits flat cochains with arbitrary prescribed
  holonomy pair), so `dim H¹ = 2` is not an artefact of a degenerate definition;
  and `finrank_torusH1` is proved from a constructed linear equivalence, not
  asserted.
* Synthesis (PI): together with `CyclicHolonomy` (`dim H¹ = 1` for the loop) this
  confirms the Betti-number reading of adversarial obstructions and gives the
  next conjecture: `dim H¹ = |E| - |V| + 1` for an arbitrary connected nerve.
-/


open BigOperators Finset

open SheafCohomologyRobustness
open TorusNerve

variable {m n : ℕ}







/-! ## §1. Elementary cyclic lemmas -/





/-! ## §2. Coboundaries are flat, and have vanishing holonomies -/




/-! ## §3. The two holonomies of a flat cochain are well defined -/

theorem SheafCohomologyRobustness.TorusNerve.rowHol_const{h v : Grid m n → ℝ} (hflat : Flat h v) (b : Fin (n + 1)) :
    rowHol h b = rowHol h 0 := by sorry
