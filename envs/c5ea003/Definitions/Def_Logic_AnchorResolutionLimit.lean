-- Prove2me | Definitions.Def_Logic_AnchorResolutionLimit
-- name    : Logic_AnchorResolutionLimit
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:48:22.964979+00:00
-- url     : https://prove2.me/theorems/362e4b6b-b705-4bb9-8778-2ba81e538e1a
-- title:
--   Aether Catalog definitions — Logic_AnchorResolutionLimit
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.AnchorResolutionLimit`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/AnchorResolutionLimit.lean by skeleton subtraction
import Mathlib
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

namespace Logic.AnchorResolution

/-- `f` grows at least at rate `m` on `s`: the inversion `R ↦ P̂` is well conditioned. -/
def Expansive (f : ℝ → ℝ) (s : Set ℝ) (m : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≤ y → m * (y - x) ≤ f y - f x

/-- `f` grows at most at rate `L` on `s`: the forward map `P̂ ↦ R` amplifies by at most `L`. -/
def LipOn (f : ℝ → ℝ) (s : Set ℝ) (L : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≤ y → f y - f x ≤ L * (y - x)

/-- The probabilities compatible with an anchor stored as `R` to precision `δ`. -/
def cell (f : ℝ → ℝ) (s : Set ℝ) (R delta : ℝ) : Set ℝ := {P | P ∈ s ∧ |f P - R| ≤ delta}




/-! ## The paper-225 rider, quantified -/




/-- The four recorded feasibility margins of paper 225's corrected table. -/
noncomputable def p225Margins : Fin 4 → ℝ := ![212 / 1000, 242 / 1000, 183 / 1000, 190 / 1000]


/-! ## A non-degenerate instance of the hypotheses -/

/-- An illustrative amplification law with a pole at `P̂ = 1`. -/
noncomputable def invLaw (P : ℝ) : ℝ := 1 / (1 - P)




end Logic.AnchorResolution


