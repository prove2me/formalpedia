-- Prove2me | solution 1 for mme_released_recursive_level2_floor_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T22:51:58.92446+00:00
-- url     : https://prove2.me/submissions/b419b817-9316-4971-9754-882c1c52bf37

import Mathlib
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_marginals
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace MME.L2Cert

theorem PG_uniform0 (i : Fin 3) (r : Fin 1104) (h : ¬ parent2 r i = 2) : PG i r 0 = 1/2 := by
  unfold PG
  rw [mme_released_recursive_level2_marginals.2.2.2 r i 0, if_neg h]
  norm_num [D]

theorem PG_uniform1 (i : Fin 3) (r : Fin 1104) (h : ¬ parent2 r i = 2) : PG i r 1 = 1/2 := by
  unfold PG
  rw [mme_released_recursive_level2_marginals.2.2.2 r i 1, if_neg h]
  norm_num [D]

theorem PG_uniform2 (i : Fin 3) (r : Fin 1104) (h : ¬ parent2 r i = 2) : PG i r 2 = 0 := by
  unfold PG
  rw [mme_released_recursive_level2_marginals.2.2.2 r i 2, if_neg h]
  norm_num [D]

/-- The certified floor of a uniform level-two mode is the certified logarithm of two. -/
theorem regFloor_uniform (i : Fin 3) (r : Fin 1104) (h : ¬ parent2 r i = 2) :
    regFloor i r Eunif = logLo 0 := by
  unfold regFloor
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  rw [PG_uniform0 i r h, PG_uniform1 i r h, PG_uniform2 i r h]
  norm_num [Eunif, qvalQ]

theorem PG_param0 (i : Fin 3) (r : Fin 1104) (h : parent2 r i = 2) :
    PG i r 0 = ((l2At r).2.2 : ℚ) / (D : ℚ) := by
  unfold PG
  rw [mme_released_recursive_level2_marginals.2.2.2 r i 0, if_pos h]
  rfl

theorem PG_param1 (i : Fin 3) (r : Fin 1104) (h : parent2 r i = 2) :
    PG i r 1 = ((D - 2 * (l2At r).2.2 : ℕ) : ℚ) / (D : ℚ) := by
  unfold PG
  rw [mme_released_recursive_level2_marginals.2.2.2 r i 1, if_pos h]
  rfl

theorem PG_param2 (i : Fin 3) (r : Fin 1104) (h : parent2 r i = 2) :
    PG i r 2 = ((l2At r).2.2 : ℚ) / (D : ℚ) := by
  unfold PG
  rw [mme_released_recursive_level2_marginals.2.2.2 r i 2, if_pos h]
  rfl

theorem logLo0 : logLo 0 = 693147180559945309417232/10^24 := by norm_num [logLo, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

theorem logHi0 : logHi 0 = 693147180559945309417233/10^24 := by norm_num [logHi, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

theorem logLo1 : logLo 1 = 1098612288668109691395245/10^24 := by norm_num [logLo, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

theorem logHi1 : logHi 1 = 1098612288668109691395246/10^24 := by norm_num [logHi, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

theorem logLo2 : logLo 2 = 1609437912434100374600759/10^24 := by norm_num [logLo, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

theorem logHi2 : logHi 2 = 1609437912434100374600760/10^24 := by norm_num [logHi, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

theorem logLo3 : logLo 3 = 1945910149055313305105352/10^24 := by norm_num [logLo, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

theorem logHi3 : logHi 3 = 1945910149055313305105353/10^24 := by norm_num [logHi, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end MME.L2Cert

theorem solution :
    (logLo 0 = 693147180559945309417232/10^24 ∧ logHi 0 = 693147180559945309417233/10^24 ∧
    logLo 1 = 1098612288668109691395245/10^24 ∧ logHi 1 = 1098612288668109691395246/10^24 ∧
    logLo 2 = 1609437912434100374600759/10^24 ∧ logHi 2 = 1609437912434100374600760/10^24 ∧
    logLo 3 = 1945910149055313305105352/10^24 ∧ logHi 3 = 1945910149055313305105353/10^24) ∧
    (∀ (i : Fin 3) (r : Fin 1104), ¬ parent2 r i = 2 →
      PG i r 0 = 1/2 ∧ PG i r 1 = 1/2 ∧ PG i r 2 = 0) ∧
    (∀ (i : Fin 3) (r : Fin 1104), ¬ parent2 r i = 2 → regFloor i r Eunif = logLo 0) ∧
    ∀ (i : Fin 3) (r : Fin 1104), parent2 r i = 2 →
      PG i r 0 = ((l2At r).2.2 : ℚ) / (D : ℚ) ∧
      PG i r 1 = ((D - 2 * (l2At r).2.2 : ℕ) : ℚ) / (D : ℚ) ∧
      PG i r 2 = ((l2At r).2.2 : ℚ) / (D : ℚ) :=
  ⟨⟨MME.L2Cert.logLo0, MME.L2Cert.logHi0, MME.L2Cert.logLo1, MME.L2Cert.logHi1,
    MME.L2Cert.logLo2, MME.L2Cert.logHi2, MME.L2Cert.logLo3, MME.L2Cert.logHi3⟩,
   fun i r h ↦ ⟨MME.L2Cert.PG_uniform0 i r h, MME.L2Cert.PG_uniform1 i r h,
     MME.L2Cert.PG_uniform2 i r h⟩,
   fun i r h ↦ MME.L2Cert.regFloor_uniform i r h,
   fun i r h ↦ ⟨MME.L2Cert.PG_param0 i r h, MME.L2Cert.PG_param1 i r h,
     MME.L2Cert.PG_param2 i r h⟩⟩
