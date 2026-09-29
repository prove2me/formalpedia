-- Prove2me | Definitions.Def_Evergreen_IdempotentCollapse2_InformationCollapse
-- name    : Evergreen_IdempotentCollapse2_InformationCollapse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:37:44.667558+00:00
-- url     : https://prove2.me/theorems/3053d91c-db4b-4742-9c8a-69453eb6c424
-- title:
--   Aether Catalog definitions — Evergreen_IdempotentCollapse2_InformationCollapse
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.IdempotentCollapse2.InformationCollapse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/IdempotentCollapse2/InformationCollapse.lean by skeleton subtraction
import Mathlib

/-!
# Direction 7: Information-Theoretic Collapse — Sufficient Statistics and Compression

## The Insight

In information theory and statistics, many operations are idempotent collapses
that reduce information while preserving what matters:

1. **Sufficient statistics**: T(x) captures all information about θ.
   Computing T(T(x)) = T(x) — sufficiency is idempotent.

2. **Lossy compression**: Compressing already-compressed data doesn't change it.
   JPEG(JPEG(image)) ≈ JPEG(image).

3. **Quantization**: Rounding to a grid is idempotent.
   round(round(x)) = round(x).

4. **Entropy**: H(X) measures information content.
   Idempotent maps cannot increase entropy.

## Main Results

* `floor_idempotent` — ⌊⌊x⌋⌋ = ⌊x⌋
* `round_idempotent` — Rounding integers is identity
* `quantization_idempotent` — Grid quantization is idempotent
* `entropy_decrease_under_collapse` — Idempotent maps reduce entropy
* `projection_decreases_rank` — Rank decreases under projection
-/

open Set Function

noncomputable section

/-! ### Floor and Ceiling are Idempotent -/




/-! ### Quantization as Idempotent Collapse -/

/-- Quantize a real number to the nearest multiple of δ. -/
def quantize (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : ℝ :=
  δ * ⌊x / δ + 1/2⌋


/-! ### Rank Decreases Under Idempotent Maps -/


/-
PROBLEM
If an idempotent has full image, it's the identity.

PROVIDED SOLUTION
If f is idempotent and |image(f)| = |α|, then f is surjective (since image = α as finite sets). But if f is surjective and idempotent, f = id: for all x, x ∈ range f, so x = f(y) for some y, and f(x) = f(f(y)) = f(y) = x. Actually, surjective + idempotent on a finite type: by Finset.card_image_eq_card_univ, f is injective. An injective idempotent: if f(x) ≠ x for some x, then f(x) is a fixed point. But f(x) ≠ x and f(f(x)) = f(x), so x maps to f(x) and f(x) maps to f(x). By injectivity x = f(x), contradiction.
-/

/-! ### Data Processing Inequality (Combinatorial Version) -/

/-
PROBLEM
Composing idempotents can only further reduce the image.
    This is a combinatorial analogue of the data processing inequality:
    processing data can never increase information.

PROVIDED SOLUTION
|image(g ∘ f)| ≤ |image(f)| because range(g∘f) ⊆ range(g), and |image(g ∘ f)| ≤ |image(g)| because g ∘ f factors through g. Use Finset.card_image_le applied to the image. Actually, image(g∘f)(univ) = image g (image f univ), so |image(g∘f)| ≤ |image f| and |image(g∘f)| ≤ |image g|.
-/

/-! ### Entropy and Collapse -/


/-! ### Projection Rank -/

 -- The deep theorem rank = trace needs more machinery

end


