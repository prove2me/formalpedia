-- Prove2me | solution 1 for mme_released_recursive_level2_potential_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T22:22:26.31456+00:00
-- url     : https://prove2.me/submissions/4a632af3-6cff-4025-ad9a-cccad7fdbc79

import Mathlib
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_certified_entropy_rational_floor
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_released_recursive_level2_marginals
import Theorems.Thm_mme_released_recursive_level2_shapes
import Theorems.Thm_mme_released_recursive_stage_level2_counts0
import Theorems.Thm_mme_released_recursive_stage_level2_counts1
import Theorems.Thm_mme_released_recursive_stage_level2_counts2
import Theorems.Thm_mme_released_recursive_stage_level2_counts3

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000


namespace MME.L2Cert

theorem wpair_zero (a b : Fin 3) : (wpair a b) 0 0 = a := rfl

theorem wpair_one (a b : Fin 3) : (wpair a b) 1 0 = b := rfl

/-- Pairs of one-letter words are pairs of letters. -/
def wpairEquiv : (Fin 3 × Fin 3) ≃ (Fin 2 → CompleteSplit.CompleteWord 1) where
  toFun x := wpair x.1 x.2
  invFun w := (w 0 0, w 1 0)
  left_inv := fun _ ↦ rfl
  right_inv := by
    intro w
    funext k z
    match k, z with
    | 0, 0 => rfl
    | 1, 0 => rfl

/-- A sum over pairs of one-letter words is a double sum over letters. -/
theorem sum_wpair (f : (Fin 2 → CompleteSplit.CompleteWord 1) → ℚ) :
    ∑ w, f w = ∑ a : Fin 3, ∑ b : Fin 3, f (wpair a b) := by
  classical
  rw [← Equiv.sum_comp wpairEquiv f, Fintype.sum_prod_type]
  rfl

/-- The level-two mixture, on a pair of letters. -/
theorem PL_wpair (i : Fin 3) (r : Fin 1104) (a b : Fin 3) :
    PL i r (wpair a b) =
      (if b.val = parent2 r i - a.val then (Jm r i a : ℚ) else 0) / (D : ℚ) := by
  rw [mme_released_recursive_level2_marginals.2.2.1 i r (wpair a b), wpair_zero, wpair_one]

end MME.L2Cert

namespace MME.L2Cert

/-- The parent grade triple of a level-two region, in vector form. -/
theorem shape_vec2 (r : Fin 1104) :
    parent2 r = ![1, 1, 2] ∨ parent2 r = ![1, 2, 1] ∨ parent2 r = ![2, 1, 1] := by
  rcases mme_released_recursive_level2_shapes.1 r with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; unfold parent2 normTriple; rw [h1, h2]; norm_num
  · right; left; unfold parent2 normTriple; rw [h1, h2]; norm_num
  · right; right; unfold parent2 normTriple; rw [h1, h2]; norm_num

theorem parent2_le (r : Fin 1104) (i : Fin 3) : parent2 r i ≤ 2 := by
  rcases shape_vec2 r with h | h | h <;> rw [h] <;> match i with
    | 0 => decide
    | 1 => decide
    | 2 => decide

/-- A sum over word pairs against the mixture collapses to a sum over the three grades. -/
theorem sum_diag (i : Fin 3) (r : Fin 1104) (hr : 0 < n2 r)
    (F : ℚ → (Fin 4 → ℤ) → ℚ) (hF : ∀ e, F 0 e = 0) (E : Fin 3 → Fin 4 → ℤ) :
    ∑ w : Fin 2 → CompleteSplit.CompleteWord 1,
      F (mixQ htotal2 n2 m2 (mu2 i) r w) (E (w 0 0)) = ∑ a : Fin 3, F (PG i r a) (E a) := by
  classical
  rw [show (fun w : Fin 2 → CompleteSplit.CompleteWord 1 ↦
      F (mixQ htotal2 n2 m2 (mu2 i) r w) (E (w 0 0))) =
      (fun w ↦ F (PL i r w) (E (w 0 0))) from by
    funext w
    rw [mme_released_recursive_level2_marginals.2.1 i r hr w]]
  rw [sum_wpair (fun w ↦ F (PL i r w) (E (w 0 0)))]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  have hc : parent2 r i - a.val < 3 := by
    have := parent2_le r i
    omega
  rw [Finset.sum_eq_single (⟨parent2 r i - a.val, hc⟩ : Fin 3)]
  · rw [PL_wpair i r a ⟨parent2 r i - a.val, hc⟩, wpair_zero, if_pos rfl]
    rfl
  · intro b _ hb
    rw [PL_wpair i r a b, wpair_zero, if_neg (fun h ↦ hb (Fin.ext h))]
    simpa using hF (E a)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A certified rational floor for one level-two region's entropy. -/
theorem region_floor (i : Fin 3) (r : Fin 1104) (hr : 0 < n2 r) (E : Fin 3 → Fin 4 → ℤ) :
    (((∑ a : Fin 3, (PG i r a - (PG i r a) ^ 2 / qvalQ (E a))) -
      ∑ j, (if 0 ≤ (∑ a : Fin 3, PG i r a * ((E a j : ℤ) : ℚ)) then
              (∑ a : Fin 3, PG i r a * ((E a j : ℤ) : ℚ)) * logHi j
            else (∑ a : Fin 3, PG i r a * ((E a j : ℤ) : ℚ)) * logLo j) : ℚ) : ℝ) ≤
      entropy (fun w ↦ ((mixQ htotal2 n2 m2 (mu2 i) r w : ℚ) : ℝ)) := by
  classical
  refine mme_certified_entropy_rational_floor.1
    (fun w ↦ mixQ htotal2 n2 m2 (mu2 i) r w)
    (fun w ↦ (mme_certified_entropy_bridge.{0, 0}.2.2.1 htotal2 n2 m2 (mu2 i) r w).1)
    (fun w ↦ E (w 0 0)) _ _ ?_ ?_
  · exact sum_diag i r hr (fun x e ↦ x - x ^ 2 / qvalQ e) (fun e ↦ by simp) E
  · exact fun j ↦ sum_diag i r hr (fun x e ↦ x * ((e j : ℤ) : ℚ)) (fun e ↦ by simp) E

end MME.L2Cert

namespace MME.L2Cert

theorem n2_pos (r : Fin 1104) : 0 < n2 r := by
  rcases lt_or_ge r.val 276 with h | h
  · exact (mme_released_recursive_stage_level2_counts0 r (Nat.zero_le _) h).1
  · rcases lt_or_ge r.val 552 with h2 | h2
    · exact (mme_released_recursive_stage_level2_counts1 r h h2).1
    · rcases lt_or_ge r.val 828 with h3 | h3
      · exact (mme_released_recursive_stage_level2_counts2 r h2 h3).1
      · exact (mme_released_recursive_stage_level2_counts3 r h3 r.isLt).1

/-- A certified rational floor for a whole level-two parent potential. -/
theorem parentPotential_floor (i : Fin 3) (E : Fin 1104 → Fin 3 → Fin 4 → ℤ) (f : Fin 1104 → ℚ)
    (hf : ∀ r, f r ≤ regFloor i r (E r)) :
    (∑ r : Fin 1104, ((n2 r : ℕ) : ℝ) * ((f r : ℚ) : ℝ)) ≤
      parentPotential htotal2 n2 m2 (mu2 i) := by
  rw [mme_certified_entropy_bridge.{0, 0}.2.2.2.1 htotal2 n2 m2 (mu2 i)]
  refine Finset.sum_le_sum (fun r _ ↦ ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans ?_ (region_floor i r (n2_pos r) (E r))
  have h := hf r
  exact_mod_cast h

end MME.L2Cert

theorem solution :
    (∀ r : Fin 1104, 0 < n2 r) ∧
    (∀ (r : Fin 1104) (i : Fin 3), parent2 r i ≤ 2) ∧
    (∀ (i : Fin 3) (r : Fin 1104) (E : Fin 3 → Fin 4 → ℤ),
      ((regFloor i r E : ℚ) : ℝ) ≤
        entropy (fun w ↦ ((mixQ htotal2 n2 m2 (mu2 i) r w : ℚ) : ℝ))) ∧
    ∀ (i : Fin 3) (E : Fin 1104 → Fin 3 → Fin 4 → ℤ) (f : Fin 1104 → ℚ),
      (∀ r, f r ≤ regFloor i r (E r)) →
      (∑ r : Fin 1104, ((n2 r : ℕ) : ℝ) * ((f r : ℚ) : ℝ)) ≤
        parentPotential htotal2 n2 m2 (mu2 i) :=
  ⟨MME.L2Cert.n2_pos, fun r i ↦ MME.L2Cert.parent2_le r i,
   fun i r E ↦ MME.L2Cert.region_floor i r (MME.L2Cert.n2_pos r) E,
   fun i E f hf ↦ MME.L2Cert.parentPotential_floor i E f hf⟩
