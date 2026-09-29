-- Prove2me | Theorems.Thm_BabelCode_card_agree_column
-- name    : BabelCode.card_agree_column
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:21:09.128258+00:00
-- url     : https://prove2.me/theorems/e8ab9b79-57a5-435e-a555-b3ff777ef01e
-- title:
--   Card agree column
-- statement:
--   Formal statement of `BabelCode.card_agree_column` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem BabelCode.card_agree_column{A L : ℕ} (C : Finset (Volume A L)) (j : Fin L) :
--       ((C ×ˢ C).filter (fun p => p.1 j = p.2 j)).card
--         = ∑ a : Fin A, ((C.filter (fun v => v j = a)).card) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/BabelCodeasanovelmathematicalstructure/SalvagedBest.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/BabelCodeasanovelmathematicalstructure/SalvagedBest.lean#L38

-- Thm stub generated from Shared/BabelCodeasanovelmathematicalstructure/SalvagedBest.lean
import Mathlib
import Definitions.Def_Shared_BabelCodeasanovelmathematicalstructure_SalvagedBest
/-
# Babel codes: Plotkin bound, Lawvere diagonal, and sphere packing

The "Volume" of the Library of Babel with alphabet size `A` and page length `L`
is the Hamming space `Fin L → Fin A`.  A *Babel code* of minimum distance `d` is
a set of volumes pairwise at Hamming distance at least `d`.

This file was recovered from a fragment whose supporting definitions
(`Volume`, `IsBabelCode`, `hammingBall`, and the column-disagreement counting
lemma) were missing.  They are supplied here and every statement is proved
from scratch, with no `sorry` and no appeal to `native_decide`.
-/

open Function

open BabelCode




/-! ## Column counting

The engine of the Plotkin bound: in a single coordinate `j`, the number of
*ordered pairs of codewords agreeing at `j`* is `∑ₐ nₐ²` where `nₐ` counts the
codewords carrying the symbol `a` in position `j`.  Cauchy–Schwarz then bounds
the number of disagreeing pairs. -/

theorem BabelCode.card_agree_column{A L : ℕ} (C : Finset (Volume A L)) (j : Fin L) :
    ((C ×ˢ C).filter (fun p => p.1 j = p.2 j)).card
      = ∑ a : Fin A, ((C.filter (fun v => v j = a)).card) ^ 2 := by sorry
