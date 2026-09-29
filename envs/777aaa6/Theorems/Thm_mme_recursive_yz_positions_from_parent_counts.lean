-- Prove2me | Theorems.Thm_mme_recursive_yz_positions_from_parent_counts
-- name    : mme_recursive_yz_positions_from_parent_counts
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T17:02:08.602777+00:00
-- url     : https://prove2.me/theorems/871c7f1c-68b8-4330-9433-b7450878f740
-- title:
--   Hash and Stage positions from row counts
-- statement:
--   Given a finite parent family with row counts n whose total is P, the disjoint union of its row indices is equivalent to Fin P, and the two-half stage-position type is equivalent to Fin (2P). These are exactly the finite position equivalences required by HashData and Stage once the main construction sets N+1=P and L=2P. This is only a finite reindexing result; it does not construct hash data or establish any stage budget.
-- source:
--   Source-faithful finite interface extracted from MME.RecursiveYZ.Position in Def_mme_recursive_yz_physical_words and the exact HashData.positions and Stage.positions fields in Def_mme_hash_extraction_certificate and Def_mme_recursive_yz_stage_certificate. The count premise is supplied by mme_more_asymmetry_stage_row_population_from_profiles (eeb9038d-2765-4ad7-98b1-4bcf86ec6f26), now Proved.

import Definitions.Def_mme_recursive_yz_physical_words
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod

open BigOperators MME.RecursiveYZ
set_option autoImplicit false

theorem mme_recursive_yz_positions_from_parent_counts {R P : ℕ} (n : Fin R → ℕ) (h : ∑ r : Fin R, n r = P) : Nonempty (Fin P ≃ ((r : Fin R) × Fin (n r))) ∧ Nonempty (Fin (2 * P) ≃ Position n) := by sorry
