-- Prove2me | Theorems.Thm_Logic_AnchorResolution_cell_mem_of_close
-- name    : Logic.AnchorResolution.cell_mem_of_close
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:25:18.414538+00:00
-- url     : https://prove2.me/theorems/0c157e8e-bf1e-48b8-8d10-064fa18cf090
-- title:
--   The cell is a genuine window.
-- statement:
--   **The cell is a genuine window.**  If `f P₀ = R` then every admissible `P` within
--   `δ/L` of `P₀` also lies in the cell: the resolution limit is not an artifact of the bound.
--
--   ```lean
--   theorem Logic.AnchorResolution.cell_mem_of_close{f : ℝ → ℝ} {s : Set ℝ} {m L R delta : ℝ} (hm : 0 ≤ m) (hL : 0 < L)
--       (hexp : Expansive f s m) (hf : LipOn f s L) {P0 P : ℝ} (hP0 : P0 ∈ s) (hP : P ∈ s)
--       (hR : f P0 = R) (hclose : |P - P0| ≤ delta / L) :
--       P ∈ cell f s R delta := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AnchorResolutionLimit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AnchorResolutionLimit.lean#L73

-- Thm stub generated from Logic/AnchorResolutionLimit.lean
import Mathlib
import Definitions.Def_Logic_AnchorResolutionLimit
/-
# Resolution-limited inversion of a booked anchor (paper 225 erratum rider)

The rider attached to the exp-576 report concerns four booked amplification anchors whose
underlying hit probability `P̂` was never stored raw: each booked `P̂` is a *drafted-law
inversion*, recovered from the stored anchor to a precision of about `2·10⁻⁴`.  The
recommendation is to book the anchors "at resolution limit" rather than "at stored `P̂`".

This file supplies the mathematics that makes "resolution limit" a definite notion and
that certifies the two quantitative claims of the rider.

**Two-sided resolution.**  For a law `f` that is at least `m`-expansive and at most
`L`-Lipschitz on a window `s`, the set of probabilities compatible with an anchor stored to
precision `δ` — the *resolution cell* — has diameter at most `2δ/m`
(`Logic.AnchorResolution.cell_diam_le`) and contains a whole interval of half-width `δ/L`
around any exact preimage (`Logic.AnchorResolution.cell_mem_of_close`).  So the cell is a
genuine window, not a point: an inversion cannot report more than the cell.

**Forward amplification.**  Conversely a `P̂` discrepancy `ε` moves the anchor by at most
`L·ε` (`Logic.AnchorResolution.anchor_shift_le`).  At the `29.1×` locus the booked
`P̂ = 0.9853` exceeds the certified-law-implied `P̂ = 0.985068` by `2.32·10⁻⁴`, and the
sensitivity of the law there is about `826`, giving an anchor overstatement of at most
`0.192` — the reported `~0.19` (`Logic.AnchorResolution.p225_printed_overstatement`).

**Margin robustness.**  Feasibility of the corrected table is unaffected: a perturbation of
the booked anchor smaller than the recorded slack cannot break `S_raw ≤ S_A`
(`Logic.AnchorResolution.feasibility_margin_stable`), and all four recorded margins
`0.212 / 0.242 / 0.183 / 0.190` exceed the perturbation
(`Logic.AnchorResolution.p225_four_margins_hold`).

An explicit non-degenerate law `P ↦ 1/(1−P)` on `[0.98, 0.99]` is carried through to show
that the expansive/Lipschitz hypotheses are satisfiable with a genuine gap between the two
constants (`Logic.AnchorResolution.invLaw_expansive`, `Logic.AnchorResolution.invLaw_lipOn`,
`Logic.AnchorResolution.invLaw_cell_width`).
-/

open Logic.AnchorResolution

theorem Logic.AnchorResolution.cell_mem_of_close{f : ℝ → ℝ} {s : Set ℝ} {m L R delta : ℝ} (hm : 0 ≤ m) (hL : 0 < L)
    (hexp : Expansive f s m) (hf : LipOn f s L) {P0 P : ℝ} (hP0 : P0 ∈ s) (hP : P ∈ s)
    (hR : f P0 = R) (hclose : |P - P0| ≤ delta / L) :
    P ∈ cell f s R delta := by sorry
