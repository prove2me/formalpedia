-- Prove2me | Definitions.Def_Novelty_HolographicCyclicInequality
-- name    : Novelty_HolographicCyclicInequality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:12:42.785125+00:00
-- url     : https://prove2.me/theorems/0b59afab-158e-4cec-b0c3-07188bd038c4
-- title:
--   Aether Catalog definitions — Novelty_HolographicCyclicInequality
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.HolographicCyclicInequality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/HolographicCyclicInequality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

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

namespace EmergentGeometry

open Finset

variable {V : Type*} [Fintype V]

/-! ## The cyclic contraction rule -/

/-- The Boolean rule producing the region assigned to the pair `A₀A₁` from the
membership pattern in the five triple-regions. -/
def cyc (c₀ c₁ c₂ c₃ c₄ : Bool) : Bool := c₄ && !c₂ && (c₀ || (c₁ && !c₃))


/-- At most one of five Boolean values is `true`: the pointwise form of pairwise
disjointness of five boundary regions. -/
def AtMostOneTrue (a₀ a₁ a₂ a₃ a₄ : Bool) : Prop :=
  a₀.toNat + a₁.toNat + a₂.toNat + a₃.toNat + a₄.toNat ≤ 1

instance (a₀ a₁ a₂ a₃ a₄ : Bool) : Decidable (AtMostOneTrue a₀ a₁ a₂ a₃ a₄) := by
  unfold AtMostOneTrue; infer_instance



/-! ## The entropy inequality -/

variable [DecidableEq V]


end EmergentGeometry


