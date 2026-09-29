-- Prove2me | Definitions.Def_mme_dwz_positive_134_integer_fine_profile_data
-- name    : mme_dwz_positive_134_integer_fine_profile_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-20T19:43:18.197171+00:00
-- url     : https://prove2.me/theorems/dcb9191a-b176-4d4d-81f8-b8f2af58386d
-- title:
--   Concrete six-region integer fine profiles for the DWZ (1,3,4) component
-- statement:
--   This is a concrete integer fine-profile candidate for the original-profile $(1,3,4)$ component at $q=5$. It uses the published object-151 regional weights and the coarse distributions in recursive witnesses 6–8, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has eight admissible coarse cells and nine actual two-letter fine words.
--
--   The fine distributions use the published $(0,2,2)$ and $(2,0,2)$ profiles, the canonical coupled $(1,1,2)$ profile from row 6 of the coupled63 data, coupled parameters $(\ell,g)=(21,479)$ in the other two interior orientations, half-half elementary profiles, and the full dimension-27 $(2,2,0)$ profile. A common denominator clears every fine probability. The definitions give concrete regional lengths, joint coarse counts, three-mode fine counts, and normalized entropy expressions for exactly those data.
--
--   Separate theorems establish normalization, boundary compatibility, preservation of the released parent profile, and quantitative entropy bounds. These definitions do not assert a tensor value or a matrix multiplication exponent bound.
-- source:
--   Published object-151 data: https://prove2.me/theorems/eca4895a-f787-4924-af5a-7e6f4fdc35ac . Coarse distributions: mme_dwz_fourth_rational_recursive_entropy_data, witnesses 6–8. Fine inputs: mme_dwz_fourth_literal022_row_data row 2; mme_dwz_fourth_literal202_row_data row 2; mme_dwz_fourth_coupled63_canonical_row_data rows 6–8. The elementary half-half and (2,2,0) full dimension-27 choices are the explicit alternative candidate documented in this definition.

import Definitions.Def_mme_dwz_positive_134_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ134Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![1, 3, 4], ![3, 1, 4], ![3, 4, 1], ![4, 3, 1], ![4, 1, 3], ![1, 4, 3]]
def shape : Fin 6 → Fin 8 → Fin 3 → Fin 5 := ![![![0, 0, 4], ![0, 1, 3], ![0, 2, 2], ![0, 3, 1], ![1, 0, 3], ![1, 1, 2], ![1, 2, 1], ![1, 3, 0]], ![![0, 0, 4], ![1, 0, 3], ![2, 0, 2], ![3, 0, 1], ![0, 1, 3], ![1, 1, 2], ![2, 1, 1], ![3, 1, 0]], ![![0, 4, 0], ![1, 3, 0], ![2, 2, 0], ![3, 1, 0], ![0, 3, 1], ![1, 2, 1], ![2, 1, 1], ![3, 0, 1]], ![![4, 0, 0], ![3, 1, 0], ![2, 2, 0], ![1, 3, 0], ![3, 0, 1], ![2, 1, 1], ![1, 2, 1], ![0, 3, 1]], ![![4, 0, 0], ![3, 0, 1], ![2, 0, 2], ![1, 0, 3], ![3, 1, 0], ![2, 1, 1], ![1, 1, 2], ![0, 1, 3]], ![![0, 4, 0], ![0, 3, 1], ![0, 2, 2], ![0, 1, 3], ![1, 3, 0], ![1, 2, 1], ![1, 1, 2], ![1, 0, 3]]]
def alphaCount : Fin 3 → Fin 8 → ℕ := ![![15571724513, 60622100347940, 426045443311346, 13316876988882, 13316875614978, 426045443013036, 60622117304962, 15571694343], ![146454313947846, 120115410051677, 119737768014960, 111214694888363, 111176963225697, 119803659595423, 124992352792464, 146504837483570], ![15325966566, 56193022117103, 430216500308975, 13575143666131, 13575142331531, 430216501356310, 56193038314134, 15325939250]]
def denominator : ℕ := 27000000000000027000000000000000
def profileCount : Fin 11 → Fin 9 → ℕ :=
  ![![27000000000000027000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 27000000000000027000000000000000], ![0, 13500000000000013500000000000000, 0, 13500000000000013500000000000000, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 13500000000000013500000000000000, 0, 13500000000000013500000000000000, 0], ![0, 0, 1300688918877915000000000000000, 0, 24398622167435865000000000000000, 0, 1300688913686247000000000000000, 0, 0], ![0, 0, 1300688913686247000000000000000, 0, 24398622167435865000000000000000, 0, 1300688918877915000000000000000, 0, 0], ![0, 0, 23964606139928775121280229147, 0, 26952070787720169449757439541706, 0, 23964606139928775121280229147, 0, 0], ![0, 0, 567000000000000567000000000000, 0, 25866000000000025866000000000000, 0, 567000000000000567000000000000, 0, 0], ![0, 0, 1000000000000001000000000000000, 0, 25000000000000025000000000000000, 0, 1000000000000001000000000000000, 0, 0], ![0, 0, 1050922428339421050922428339420, 0, 24898155142339707898155142339683, 0, 1050922429320898050922429320897, 0, 0], ![0, 0, 1050922429320898050922429320897, 0, 24898155142339707898155142339683, 0, 1050922428339421050922428339420, 0, 0]]
def profileIndex : Fin 6 → Fin 8 → Fin 3 → Fin 11 :=
  ![![![0, 0, 1], ![0, 2, 3], ![0, 4, 5], ![0, 3, 2], ![2, 0, 3], ![2, 2, 6], ![2, 7, 2], ![2, 3, 0]], ![![0, 0, 1], ![2, 0, 3], ![4, 0, 5], ![3, 0, 2], ![0, 2, 3], ![2, 2, 6], ![7, 2, 2], ![3, 2, 0]], ![![0, 1, 0], ![2, 3, 0], ![8, 8, 0], ![3, 2, 0], ![0, 3, 2], ![2, 7, 2], ![7, 2, 2], ![3, 0, 2]], ![![1, 0, 0], ![3, 2, 0], ![8, 8, 0], ![2, 3, 0], ![3, 0, 2], ![7, 2, 2], ![2, 7, 2], ![0, 3, 2]], ![![1, 0, 0], ![3, 0, 2], ![9, 0, 10], ![2, 0, 3], ![3, 2, 0], ![7, 2, 2], ![2, 2, 6], ![0, 2, 3]], ![![0, 1, 0], ![0, 3, 2], ![0, 9, 10], ![0, 2, 3], ![2, 3, 0], ![2, 7, 2], ![2, 2, 6], ![2, 0, 3]]]

def fineCount (r : Fin 6) (j : Fin 8) (i : Fin 3) (w : Fin 9) : ℕ :=
  profileCount (profileIndex r j i) w

def word : Fin 9 → CompleteSplit.CompleteWord 2 :=
  ![![0,0],![0,1],![0,2],![1,0],![1,1],![1,2],![2,0],![2,1],![2,2]]

/-- The nine actual two-letter words, in lexicographic order. -/
noncomputable def wordEquiv : Fin 9 ≃ CompleteSplit.CompleteWord 2 :=
  Equiv.ofBijective word (by decide +kernel)

/-- The eight admissible left-half grades in each physical orientation. -/
def splitMap (r : Fin 6) (j : Fin 8) : RecursiveThinSplit.Split 4 (parent r) :=
  ⟨shape r j, by
    have h : ∀ r j,
      (shape r j 0).val + (shape r j 1).val + (shape r j 2).val = 4 ∧
        ∀ i, (shape r j i).val ≤ parent r i := by decide +kernel
    exact h r j⟩

noncomputable def splitEquiv (r : Fin 6) : Fin 8 ≃ RecursiveThinSplit.Split 4 (parent r) :=
  Equiv.ofBijective (splitMap r) (by
    have h : ∀ r, Function.Bijective (splitMap r) := by decide +kernel
    exact h r)

theorem parent_total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * 4 := by decide +kernel

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent134.regionalWeight (region r)
def n (r : Fin 6) : ℕ := weightCount r * 1000000000000000 * denominator
noncomputable def m (r : Fin 6) (c : RecursiveThinSplit.Split 4 (parent r)) : ℕ :=
  weightCount r * alphaCount (region r) ((splitEquiv r).symm c) * denominator
noncomputable def mu (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteSplit.CompleteWord 2) : ℕ :=
  let j := (splitEquiv c.1).symm c.2
  weightCount c.1 * (alphaCount (region c.1) j + alphaCount (region c.1) (Fin.rev j)) *
    fineCount c.1 j i (wordEquiv.symm w)
def totalCount : ℕ := 2000000000000000000000000000000 * denominator

/-- Normalized formulas used to certify the entropy of the same integer data. -/
def weight (r : Fin 6) : ℚ := (weightCount r : ℚ) / 2000000000000000
def alpha (r : Fin 6) (j : Fin 8) : ℚ := (alphaCount (region r) j : ℚ) / 1000000000000000
def beta (r : Fin 6) (j : Fin 8) (i : Fin 3) (w : Fin 9) : ℚ :=
  (fineCount r j i w : ℚ) / denominator

def coarse (r : Fin 6) (i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ j : Fin 8, if shape r j i = g then alpha r j else 0

def jointWord (r : Fin 6) (i : Fin 3) (a b : Fin 9) : ℚ :=
  ∑ j : Fin 8, alpha r j * beta r j i a * beta r (Fin.rev j) i b

def boundary (i : Fin 2) (r : Fin 6) (j : Fin 8) : Bool :=
  if i = 0 then shape r j 2 = 0 else shape r j 0 = 0 ∨ shape r j 1 = 0

/-- Individual boundary parts 0..7 and grouped interior parts 8..12. -/
def partMass (i : Fin 2) (r : Fin 6) (s : Fin 13) (w : Fin 9) : ℚ :=
  ∑ j : Fin 8,
    if (if boundary i r j then j.val else 8 + (shape r j (yzMode i)).val) = s.val
    then (alpha r j + alpha r (Fin.rev j)) * beta r j (yzMode i) w else 0

noncomputable def ratEntropy {t : ℕ} (p : Fin t → ℚ) : ℝ :=
  ∑ j, Real.negMulLog (p j : ℝ)
noncomputable def ratMassEntropy {t : ℕ} (p : Fin t → ℚ) : ℝ :=
  ratEntropy p - Real.negMulLog ((∑ j, p j : ℚ) : ℝ)
noncomputable def coarseRate : ℝ :=
  ∑ r, (weight r : ℝ) * ratEntropy (coarse r 0)
noncomputable def parentRate (i : Fin 3) : ℝ :=
  ∑ r, (weight r : ℝ) * ∑ a, ∑ b, Real.negMulLog (jointWord r i a b : ℝ)
noncomputable def compatibilityRate (i : Fin 2) : ℝ :=
  ∑ r, (weight r : ℝ) * ∑ s, ratMassEntropy (partMass i r s)
noncomputable def explicitRate : ℝ :=
  min coarseRate (min (parentRate 1 - compatibilityRate 0) (parentRate 2 - compatibilityRate 1))

end MME.DWZ134Fine


