-- Prove2me | solution 1 for mme_released_recursive_level2_pen9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:35:14.264982+00:00
-- url     : https://prove2.me/submissions/9c96287c-6e3c-4199-a7a4-f084ea023bf6

import Mathlib
import Definitions.Def_mme_released_recursive_level2_penalty_data
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_marginals
import Theorems.Thm_mme_released_recursive_level2_penalty_tools
import Theorems.Thm_mme_released_recursive_level2_pen9a
import Theorems.Thm_mme_released_recursive_level2_pen9b

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000



theorem solution : ∀ j : Fin 46,
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨414 + j.val, by omega⟩),
        qvalQ (fun t ↦ ∑ i, PE ⟨414 + j.val, by omega⟩ i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨414 + j.val, by omega⟩),
        (alphaQ ⟨414 + j.val, by omega⟩ c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE ⟨414 + j.val, by omega⟩ i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  intro j
  have hP : ∀ k k' : Fin 1104, k = k' → (fun k : Fin 1104 => ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 k),
        qvalQ (fun t ↦ ∑ i, PE k i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 k),
        (alphaQ k c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE k i (c.val i) t)) ≤
      1/(5 * 10^7)) k → (fun k : Fin 1104 => ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 k),
        qvalQ (fun t ↦ ∑ i, PE k i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 k),
        (alphaQ k c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE k i (c.val i) t)) ≤
      1/(5 * 10^7)) k' := by
    intro k k' hkk h; subst hkk; exact h
  by_cases h : j.val < 23
  · exact mme_released_recursive_level2_pen9a ⟨j.val, h⟩
  · exact hP ⟨437 + (j.val - 23), by omega⟩ ⟨414 + j.val, by omega⟩ (Fin.ext (by simp only; omega)) (mme_released_recursive_level2_pen9b ⟨j.val - 23, by omega⟩)
