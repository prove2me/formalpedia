-- Prove2me | Theorems.Thm_EmergentGeometry_cutWeight_cyclic5
-- name    : EmergentGeometry.cutWeight_cyclic5
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:36:41.00199+00:00
-- url     : https://prove2.me/theorems/0461c5b8-b34a-4ba7-9023-7d5f8d0ba30d
-- title:
--   The cut-area form of the cyclic contraction inequality.
-- statement:
--   The cut-area form of the cyclic contraction inequality.
--
--   ```lean
--   theorem EmergentGeometry.cutWeight_cyclic5(G : BulkGraph V) (f₀ f₁ f₂ f₃ f₄ : Region V) :
--       cutWeight G (fun v => cyc (f₀ v) (f₁ v) (f₂ v) (f₃ v) (f₄ v))
--         + cutWeight G (fun v => cyc (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₀ v))
--         + cutWeight G (fun v => cyc (f₂ v) (f₃ v) (f₄ v) (f₀ v) (f₁ v))
--         + cutWeight G (fun v => cyc (f₃ v) (f₄ v) (f₀ v) (f₁ v) (f₂ v))
--         + cutWeight G (fun v => cyc (f₄ v) (f₀ v) (f₁ v) (f₂ v) (f₃ v))
--         + cutWeight G (fun v => f₀ v || f₁ v || f₂ v || f₃ v || f₄ v)
--         ≤ cutWeight G f₀ + cutWeight G f₁ + cutWeight G f₂ + cutWeight G f₃
--           + cutWeight G f₄ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/HolographicCyclicInequality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/HolographicCyclicInequality.lean#L73

-- Thm stub generated from Novelty/HolographicCyclicInequality.lean
import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicCyclicInequality

/-!
# The five-party cyclic inequality of the holographic entropy cone

Subadditivity and strong subadditivity hold for *every* quantum state, and
monogamy of mutual information (proved in `Novelty.EmergentGeometryEntropyCone`)
is the first inequality special to geometric states.  The next genuinely new
family starts at five parties with the **cyclic inequality**

`∑_{j} S(A_j A_{j+1} A_{j+2}) ≥ ∑_{j} S(A_j A_{j+1}) + S(A_0A_1A_2A_3A_4)`,

indices mod `5`.  Here it is proved for min-cut entropies of an arbitrary finite
bulk geometry.

The proof follows the *contraction map* pattern: five minimal surfaces (one for
each cyclic triple) are recombined into six new regions — five "cyclic minority"
regions and their union — by the single Boolean rule

`cyc c₀ c₁ c₂ c₃ c₄ = c₄ ∧ ¬c₂ ∧ (c₀ ∨ (c₁ ∧ ¬c₃))`

applied to the five cyclic rotations of the membership pattern.  The two facts
that make this work are `sepBit_cyclic5` (a `1024`-case Boolean contraction
inequality) and `cyc_boundary` (the recombined regions have exactly the right
boundary traces).  The rule is *not* an intersection: no combination built from
plain intersections and unions can satisfy the contraction inequality.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V]

/-! ## The cyclic contraction rule -/

theorem EmergentGeometry.cutWeight_cyclic5(G : BulkGraph V) (f₀ f₁ f₂ f₃ f₄ : Region V) :
    cutWeight G (fun v => cyc (f₀ v) (f₁ v) (f₂ v) (f₃ v) (f₄ v))
      + cutWeight G (fun v => cyc (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₀ v))
      + cutWeight G (fun v => cyc (f₂ v) (f₃ v) (f₄ v) (f₀ v) (f₁ v))
      + cutWeight G (fun v => cyc (f₃ v) (f₄ v) (f₀ v) (f₁ v) (f₂ v))
      + cutWeight G (fun v => cyc (f₄ v) (f₀ v) (f₁ v) (f₂ v) (f₃ v))
      + cutWeight G (fun v => f₀ v || f₁ v || f₂ v || f₃ v || f₄ v)
      ≤ cutWeight G f₀ + cutWeight G f₁ + cutWeight G f₂ + cutWeight G f₃
        + cutWeight G f₄ := by sorry
