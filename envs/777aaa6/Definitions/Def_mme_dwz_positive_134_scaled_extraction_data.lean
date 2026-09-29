-- Prove2me | Definitions.Def_mme_dwz_positive_134_scaled_extraction_data
-- name    : mme_dwz_positive_134_scaled_extraction_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-20T20:43:24.867539+00:00
-- url     : https://prove2.me/theorems/2835e03f-92cd-4251-9bde-4ac132f6b885
-- title:
--   Square-scaled DWZ (1,3,4) profiles and the released regional source
-- statement:
--   For each natural scale $k$, multiply the previously verified six-region integer lengths, coarse cell counts, and three-mode fine word counts by $k^2$. The source is an actual all-mode coordinate projection of a power of the elementary CW5 tensor, with a fixed enumeration of both halves of each regional parent occurrence.
--
--   Every parent occurrence has the prescribed parent grade in each mode. In the mode corresponding to the original Z coordinate of that region's physical orientation, the histogram of left-half grades is exactly the released regional profile, multiplied by $k^2$, its released region weight, and the common fine-profile denominator. This source is defined by those parent grades and regional marginals; it does not prescribe the full joint split distribution or the fine cell profiles.
--
--   For each reference coarse address, the output predicate specifies the exact cell grades and the square-scaled useful fine profiles. Separate theorems construct integer extraction steps and actual tensor restrictions with these source and output predicates. Identification with the original prescribed-Z constituent powers remains a separate coordinate-transport argument.
-- source:
--   Concrete scaling of mme_dwz_positive_134_integer_fine_profile_data, using the existing ProfiledCW coordinate projection and the regional profiles of mme_dwz_positive_134_regional_profile_data.

import Definitions.Def_mme_dwz_positive_134_integer_fine_profile_data
import Definitions.Def_mme_integer_regional_CW_recipe

open BigOperators MME MME.RecursiveYZ MME.ProfiledCW
open scoped Classical
set_option autoImplicit false
namespace MME.DWZ134Scaled

/-- Square-scaled region lengths, with repair scale k to be supplied separately. -/
def n (k : ℕ) (r : Fin 6) : ℕ := k ^ 2 * DWZ134Fine.n r
noncomputable def m (k : ℕ) (r : Fin 6)
    (c : RecursiveThinSplit.Split 4 (DWZ134Fine.parent r)) : ℕ := k ^ 2 * DWZ134Fine.m r c
noncomputable def mu (k : ℕ) (i : Fin 3) (c : Cell 4 6 DWZ134Fine.parent)
    (w : CompleteSplit.CompleteWord 2) : ℕ := k ^ 2 * DWZ134Fine.mu i c w

def blocks (k : ℕ) : ℕ := Fintype.card (Position (n k))
def length (k : ℕ) : ℕ := blocks k * 2
noncomputable def positions (k : ℕ) : Fin (blocks k) ≃ Position (n k) :=
  (Fintype.equivFin (Position (n k))).symm

theorem length_eq (k : ℕ) : blocks k * 2 ^ (2 - 1) = length k := by rfl

/-- The independent regional source: prescribed parent grades in every block,
and the released original-Z marginal in its physical orientation. This does
not require the joint coarse distribution or the fine cell profiles. -/
def source (k : ℕ) : Predicate (length k) := fun i x ↦
  let f := ProfiledCW.split (positions k) (length_eq k) x
  (∀ r j, (∑ h : Fin 2, ∑ w : Fin 2, (f ⟨r,j,h⟩ w).val) = DWZ134Fine.parent r i) ∧
  (∀ r, i = DWZ134Fine.keptMode r → ∀ g : Fin 5,
    (Finset.univ.filter (fun j : Fin (n k r) ↦
      (∑ w : Fin 2, (f ⟨r,j,0⟩ w).val) = g.val)).card =
      k ^ 2 * DWZ134Fine.weightCount r *
        (DWZPositiveComponent134.regionalProfile (DWZ134Fine.region r)).count g * DWZ134Fine.denominator)

/-- The concrete exact-profile output over a reference coarse address. -/
def output (k : ℕ) (a : Address 4 6 DWZ134Fine.parent (n k)) : Predicate (length k) :=
  fun i x ↦
    Graded DWZ134Fine.parent_total i a (ProfiledCW.split (positions k) (length_eq k) x) ∧
      Useful (fullCell DWZ134Fine.parent_total a) (mu k i)
        (ProfiledCW.split (positions k) (length_eq k) x)

end MME.DWZ134Scaled


