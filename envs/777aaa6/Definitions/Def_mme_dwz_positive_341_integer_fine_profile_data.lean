-- Prove2me | Definitions.Def_mme_dwz_positive_341_integer_fine_profile_data
-- name    : mme_dwz_positive_341_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T16:41:09.605884+00:00
-- url     : https://prove2.me/theorems/90ad0d8c-5aa2-4ad1-bc48-21a83975da99
-- title:
--   Concrete four-region integer fine profiles for the DWZ (3,4,1) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(3,4,1)$ component at $q=5$. It uses the published object-167 regional weights and regional coarse distributions, in the two cyclic orientations of the regions with positive weight (the released weight of region 0 is zero), each paired with its X/Y swap. Each of the four physical regions has 8 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here.
-- source:
--   Released q=5 fourth-power certificate (object 167), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_341_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ341Fine

def region : Fin 4 → Fin 3 := ![1,1,2,2]
def keptMode : Fin 4 → Fin 3 := ![1,0,0,1]
def parent : Fin 4 → Fin 3 → ℕ := ![![4, 1, 3], ![1, 4, 3], ![1, 3, 4], ![3, 1, 4]]
def shape : Fin 4 → Fin 8 → Fin 3 → Fin 5 := ![![![3, 1, 0], ![4, 0, 0], ![2, 1, 1], ![3, 0, 1], ![1, 1, 2], ![2, 0, 2], ![0, 1, 3], ![1, 0, 3]], ![![1, 3, 0], ![0, 4, 0], ![1, 2, 1], ![0, 3, 1], ![1, 1, 2], ![0, 2, 2], ![1, 0, 3], ![0, 1, 3]], ![![1, 0, 3], ![0, 0, 4], ![1, 1, 2], ![0, 1, 3], ![1, 2, 1], ![0, 2, 2], ![1, 3, 0], ![0, 3, 1]], ![![0, 1, 3], ![0, 0, 4], ![1, 1, 2], ![1, 0, 3], ![2, 1, 1], ![2, 0, 2], ![3, 1, 0], ![3, 0, 1]]]
def alphaCount : Fin 3 → Fin 8 → ℕ := ![![131470331637811, 112799549563809, 128250724856293, 127472192152065, 127469019437512, 128261077666126, 112794686182195, 131482418504189], ![12437253701221, 351127357444, 420790571995264, 66421046936078, 66421046938509, 420790572019539, 351127357516, 12437253694429], ![13434493678348, 300636360796, 420302581899516, 65962288058624, 65962288053622, 420302581913721, 300636360864, 13434493674509]]
def denominator : ℕ := 111111111111111111111111111111000000000000000000000000000000
def profileCount : Fin 12 → Fin 9 → ℕ :=
  ![![111111111111111111111111111111000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 55555555555555555555555555555500000000000000000000000000000, 0, 55555555555555555555555555555500000000000000000000000000000, 0], ![0, 55555555555555555555555555555500000000000000000000000000000, 0, 55555555555555555555555555555500000000000000000000000000000, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 111111111111111111111111111111000000000000000000000000000000], ![0, 0, 2333333333333333333333333333331000000000000000000000000000, 0, 106444444444444444444444444444338000000000000000000000000000, 0, 2333333333333333333333333333331000000000000000000000000000, 0, 0], ![0, 0, 4114905657637666666666666666662551761009029000000000000000, 0, 102881299743585555555555555555452674255811970000000000000000, 0, 4114905709887888888888888888884773983179001000000000000000, 0, 0], ![0, 0, 4114905709887888888888888888884773983179001000000000000000, 0, 102881299743585555555555555555452674255811970000000000000000, 0, 4114905657637666666666666666662551761009029000000000000000, 0, 0], ![0, 0, 92758525960221038075550924722767438818527422632939460193, 0, 110925594059190669034960009261554465122362945154734121079614, 0, 92758525960221038075550924722767438818527422632939460193, 0, 0], ![0, 0, 4367686831353555555555555555551187868724202000000000000000, 0, 102375737448366777777777777777675402040329411000000000000000, 0, 4367686831390777777777777777773410090946387000000000000000, 0, 0], ![0, 0, 4367686831390777777777777777773410090946387000000000000000, 0, 102375737448366777777777777777675402040329411000000000000000, 0, 4367686831353555555555555555551187868724202000000000000000, 0, 0], ![0, 0, 5354299944251666666666666666661312366722415000000000000000, 0, 100402511237866555555555555555455153044317689000000000000000, 0, 5354299928992888888888888888883534588959896000000000000000, 0, 0], ![0, 0, 5354299928992888888888888888883534588959896000000000000000, 0, 100402511237866555555555555555455153044317689000000000000000, 0, 5354299944251666666666666666661312366722415000000000000000, 0, 0]]
def profileIndex : Fin 4 → Fin 8 → Fin 3 → Fin 12 :=
  ![![![1, 2, 0], ![3, 0, 0], ![4, 2, 2], ![1, 0, 2], ![2, 2, 7], ![8, 0, 9], ![0, 2, 1], ![2, 0, 1]], ![![2, 1, 0], ![0, 3, 0], ![2, 4, 2], ![0, 1, 2], ![2, 2, 7], ![0, 8, 9], ![2, 0, 1], ![0, 2, 1]], ![![2, 0, 1], ![0, 0, 3], ![2, 2, 7], ![0, 2, 1], ![2, 4, 2], ![0, 10, 11], ![2, 1, 0], ![0, 1, 2]], ![![0, 2, 1], ![0, 0, 3], ![2, 2, 7], ![2, 0, 1], ![4, 2, 2], ![10, 0, 11], ![1, 2, 0], ![1, 0, 2]]]

def fineCount (r : Fin 4) (j : Fin 8) (i : Fin 3) (w : Fin 9) : ℕ :=
  profileCount (profileIndex r j i) w

def word : Fin 9 → CompleteSplit.CompleteWord 2 :=
  ![![0,0],![0,1],![0,2],![1,0],![1,1],![1,2],![2,0],![2,1],![2,2]]

/-- The nine actual two-letter words, in lexicographic order. -/
noncomputable def wordEquiv : Fin 9 ≃ CompleteSplit.CompleteWord 2 :=
  Equiv.ofBijective word (by decide +kernel)

/-- The eight admissible left-half grades in each physical orientation. -/
def splitMap (r : Fin 4) (j : Fin 8) : RecursiveThinSplit.Split 4 (parent r) :=
  ⟨shape r j, by
    have h : ∀ r j,
      (shape r j 0).val + (shape r j 1).val + (shape r j 2).val = 4 ∧
        ∀ i, (shape r j i).val ≤ parent r i := by decide +kernel
    exact h r j⟩

noncomputable def splitEquiv (r : Fin 4) : Fin 8 ≃ RecursiveThinSplit.Split 4 (parent r) :=
  Equiv.ofBijective (splitMap r) (by
    have h : ∀ r, Function.Bijective (splitMap r) := by decide +kernel
    exact h r)

theorem parent_total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * 4 := by decide +kernel

def weightCount (r : Fin 4) : ℕ := DWZPositiveComponent341.regionalWeight (region r)
def n (r : Fin 4) : ℕ := weightCount r * 1000000000000000 * denominator
noncomputable def m (r : Fin 4) (c : RecursiveThinSplit.Split 4 (parent r)) : ℕ :=
  weightCount r * alphaCount (region r) ((splitEquiv r).symm c) * denominator
noncomputable def mu (i : Fin 3) (c : Cell 4 4 parent) (w : CompleteSplit.CompleteWord 2) : ℕ :=
  let j := (splitEquiv c.1).symm c.2
  weightCount c.1 * (alphaCount (region c.1) j + alphaCount (region c.1) (Fin.rev j)) *
    fineCount c.1 j i (wordEquiv.symm w)
def totalCount : ℕ := 2000000000000000000000000000000 * denominator

/-- Normalized formulas used to certify the entropy of the same integer data. -/
def weight (r : Fin 4) : ℚ := (weightCount r : ℚ) / 2000000000000000
def alpha (r : Fin 4) (j : Fin 8) : ℚ := (alphaCount (region r) j : ℚ) / 1000000000000000
def beta (r : Fin 4) (j : Fin 8) (i : Fin 3) (w : Fin 9) : ℚ :=
  (fineCount r j i w : ℚ) / denominator

def coarse (r : Fin 4) (i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ j : Fin 8, if shape r j i = g then alpha r j else 0

def jointWord (r : Fin 4) (i : Fin 3) (a b : Fin 9) : ℚ :=
  ∑ j : Fin 8, alpha r j * beta r j i a * beta r (Fin.rev j) i b

def boundary (i : Fin 2) (r : Fin 4) (j : Fin 8) : Bool :=
  if i = 0 then shape r j 2 = 0 else shape r j 0 = 0 ∨ shape r j 1 = 0

/-- Individual boundary parts 0..7 and grouped interior parts 8..12. -/
def partMass (i : Fin 2) (r : Fin 4) (s : Fin 13) (w : Fin 9) : ℚ :=
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

end MME.DWZ341Fine


