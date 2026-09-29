-- Prove2me | Theorems.Thm_Catalog_Combinatorics_Reconstruction_kelly_double_count
-- name    : Catalog.Combinatorics.Reconstruction.kelly_double_count
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:02:58.340687+00:00
-- url     : https://prove2.me/theorems/2921fa22-b3a9-43ad-b793-91e125bc852f
-- title:
--   Kelly's double-counting identity: every `k`-vertex member of `A` survives
-- statement:
--   Kelly's double-counting identity: every `k`-vertex member of `A` survives
--   in exactly `|V|-k` cards.
--
--   ```lean
--   theorem Catalog.Combinatorics.Reconstruction.kelly_double_count[Fintype V] [DecidableEq V]
--       (A : Finset (Finset V)) (k : ℕ) (hA : UniformFamily A k) :
--       ∑ v : V, (survivingSets A v).card = (Fintype.card V - k) * A.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Reconstruction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Reconstruction.lean#L36

-- Thm stub generated from Combinatorics/Reconstruction.lean
import Mathlib
import Definitions.Def_Combinatorics_Reconstruction

/-!
# Vertex-deleted decks and Kelly's counting lemma

The full reconstruction conjecture is open.  This file develops its standard
finite-graph language, proves the double-counting core of Kelly's lemma, and
proves reconstruction for the two extremal graph classes: edgeless and complete
graphs.
-/

open Catalog.Combinatorics.Reconstruction

open Finset SimpleGraph
open scoped Sym2

variable {V W U : Type*}

theorem Catalog.Combinatorics.Reconstruction.kelly_double_count[Fintype V] [DecidableEq V]
    (A : Finset (Finset V)) (k : ℕ) (hA : UniformFamily A k) :
    ∑ v : V, (survivingSets A v).card = (Fintype.card V - k) * A.card := by sorry
