-- Prove2me | Definitions.Def_mme_dwz_global_common_state_broken_copy
-- name    : mme_dwz_global_common_state_broken_copy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T19:41:23.198384+00:00
-- url     : https://prove2.me/theorems/c9d61767-3a22-4b02-a184-da01be2db4d9
-- title:
--   Common-state broken copies for global DWZ retention
-- statement:
--   Fix one affine hashing state and a finite family of retained exact-profile Table-2 outer words. For each owner, a competing outer word is compatible when it has the same complete coarse-Z address, satisfies the fine Table-2 incidence conditions for the chosen useful block, and obeys the second-hash equality at that single common affine state. The resulting broken copy keeps exactly the useful blocks for which the owner is unique among all compatible competitors.
--
--   The normalized quantity
--
--   $$
--   \eta_r=\frac{|\operatorname{nonholes}(B_r)|}{|\operatorname{UsefulBlock}(r)|}
--   $$
--
--   is the nonhole mass contributed by owner $r$. Summing these fractions is the aggregate form of Claim 6.8 used by the paper; it does not assert that every owner is individually good.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 6.3 and Claim 6.8; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_affine_hash_bucket
import Definitions.Def_mme_dwz_retained_fine_compatibility
import Definitions.Def_mme_dwz_step2_broken_copy
import Definitions.Def_mme_dwz_table2_useful_block

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZGlobalCorrelated

/-- Undo the first-hash coordinate reindexing, returning to the literal
source-coordinate order used by `brokenAddressObj`. -/
def sourceWord {N L n : ℕ} (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15) (r : Fin n) :
    Fin L → Fin 15 :=
  fun t ↦ edge r (reindex.symm t)

/-- Two retained owners have the same complete coarse-Z address. -/
def sameCoarseZ {N n : ℕ}
    (edge : Fin n → Fin (N + 1) → Fin 15) (r j : Fin n) : Prop :=
  ∀ t, MME.DWZSquare.shapeZ (edge j t) =
    MME.DWZSquare.shapeZ (edge r t)

/-- The second-hash equality evaluated at the same affine state that defines
the global first-hash bucket. -/
def commonStateHashRetained {p N n : ℕ}
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15) (r j : Fin n) : Prop :=
  let ω := MME.dwzAsymmetricHashStateOfAffine q
  MME.dwzAsymmetricHashX ω (MME.dwzTable2CastX (edge j)) =
    MME.dwzAsymmetricHashZ (4 : ZMod p) ω
      (MME.dwzTable2CastZ (edge r))

/-- A competitor for owner `r` shares its complete coarse-Z address, obeys
the fine Table-2 incidence constraints, and survives at the common state's
weight. -/
def ownerCompatible
    (m : ℕ) {p N L n : ℕ} (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15) (r : Fin n)
    (z : MME.DWZTable2StandardForm.UsefulBlock m
      (sourceWord reindex edge r)) (j : Fin n) : Prop :=
  sameCoarseZ edge r j ∧
    MME.DWZStep2Source.retainedFineCompatible m
      (sourceWord reindex edge)
      (fun t ↦ MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2) j ∧
    commonStateHashRetained q edge r j

/-- The literal broken copy obtained when all owners use the one selected
global affine state. -/
noncomputable def commonStateBrokenCopy
    (m : ℕ) {p N L n : ℕ} (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15) (r : Fin n) :
    MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m
        (sourceWord reindex edge r)) := by
  classical
  exact MME.DWZStep2.brokenCopy
    (ownerCompatible m reindex q edge r) (fun _ _ ↦ True) r

/-- Normalized nonhole mass of one common-state broken copy. -/
noncomputable def nonholeFraction
    (m : ℕ) {p N L n : ℕ} (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15) (r : Fin n) : ℝ :=
  ((commonStateBrokenCopy m reindex q edge r).nonholes.card : ℝ) /
    (Fintype.card (MME.DWZTable2StandardForm.UsefulBlock m
      (sourceWord reindex edge r)) : ℝ)

end MME.DWZGlobalCorrelated


