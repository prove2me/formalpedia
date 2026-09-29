-- Prove2me | Theorems.Thm_EmergentGeometry_entropy_cyclic5
-- name    : EmergentGeometry.entropy_cyclic5
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:39:49.469541+00:00
-- url     : https://prove2.me/theorems/1c2070d6-2dc5-495a-adae-e735de46f260
-- title:
--   The five-party cyclic holographic entropy inequality.
-- statement:
--   **The five-party cyclic holographic entropy inequality.**  For pairwise
--   disjoint boundary regions `A₀,…,A₄`,
--
--   `S(A₀A₁) + S(A₁A₂) + S(A₂A₃) + S(A₃A₄) + S(A₄A₀) + S(A₀A₁A₂A₃A₄)`
--   `  ≤ S(A₀A₁A₂) + S(A₁A₂A₃) + S(A₂A₃A₄) + S(A₃A₄A₀) + S(A₄A₀A₁)`.
--
--   Unlike subadditivity and strong subadditivity, this inequality is *false* for
--   general quantum states; it is a signature of geometric (holographic)
--   entanglement, and it is not implied by monogamy of mutual information.
--
--   ```lean
--   theorem EmergentGeometry.entropy_cyclic5(M : HoloModel V) (A₀ A₁ A₂ A₃ A₄ : Region V)
--       (hd : ∀ v, AtMostOneTrue (A₀ v) (A₁ v) (A₂ v) (A₃ v) (A₄ v)) :
--       entropy M (fun v => A₀ v || A₁ v) + entropy M (fun v => A₁ v || A₂ v)
--           + entropy M (fun v => A₂ v || A₃ v) + entropy M (fun v => A₃ v || A₄ v)
--           + entropy M (fun v => A₄ v || A₀ v)
--           + entropy M (fun v => A₀ v || A₁ v || A₂ v || A₃ v || A₄ v)
--         ≤ entropy M (fun v => A₀ v || A₁ v || A₂ v)
--           + entropy M (fun v => A₁ v || A₂ v || A₃ v)
--           + entropy M (fun v => A₂ v || A₃ v || A₄ v)
--           + entropy M (fun v => A₃ v || A₄ v || A₀ v)
--           + entropy M (fun v => A₄ v || A₀ v || A₁ v) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/HolographicCyclicInequality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/HolographicCyclicInequality.lean#L103

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







/-! ## The entropy inequality -/

variable [DecidableEq V]

theorem EmergentGeometry.entropy_cyclic5(M : HoloModel V) (A₀ A₁ A₂ A₃ A₄ : Region V)
    (hd : ∀ v, AtMostOneTrue (A₀ v) (A₁ v) (A₂ v) (A₃ v) (A₄ v)) :
    entropy M (fun v => A₀ v || A₁ v) + entropy M (fun v => A₁ v || A₂ v)
        + entropy M (fun v => A₂ v || A₃ v) + entropy M (fun v => A₃ v || A₄ v)
        + entropy M (fun v => A₄ v || A₀ v)
        + entropy M (fun v => A₀ v || A₁ v || A₂ v || A₃ v || A₄ v)
      ≤ entropy M (fun v => A₀ v || A₁ v || A₂ v)
        + entropy M (fun v => A₁ v || A₂ v || A₃ v)
        + entropy M (fun v => A₂ v || A₃ v || A₄ v)
        + entropy M (fun v => A₃ v || A₄ v || A₀ v)
        + entropy M (fun v => A₄ v || A₀ v || A₁ v) := by sorry
