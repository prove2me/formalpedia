-- Prove2me | Definitions.Def_mme_dwz_positive_152_integer_fine_profile_data
-- name    : mme_dwz_positive_152_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T16:08:21.67068+00:00
-- url     : https://prove2.me/theorems/639c4b5b-a4e9-44f8-91da-e08de73625b4
-- title:
--   Concrete six-region integer fine profiles for the DWZ (1,5,2) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(1,5,2)$ component at $q=5$. It uses the published object-153 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 6 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here.
-- source:
--   Released q=5 fourth-power certificate (object 153), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_152_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ152Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![1, 5, 2], ![5, 1, 2], ![5, 2, 1], ![2, 5, 1], ![2, 1, 5], ![1, 2, 5]]
def shape : Fin 6 → Fin 6 → Fin 3 → Fin 5 := ![![![0, 2, 2], ![0, 3, 1], ![0, 4, 0], ![1, 1, 2], ![1, 2, 1], ![1, 3, 0]], ![![2, 0, 2], ![3, 0, 1], ![4, 0, 0], ![1, 1, 2], ![2, 1, 1], ![3, 1, 0]], ![![2, 2, 0], ![3, 1, 0], ![4, 0, 0], ![1, 2, 1], ![2, 1, 1], ![3, 0, 1]], ![![2, 2, 0], ![1, 3, 0], ![0, 4, 0], ![2, 1, 1], ![1, 2, 1], ![0, 3, 1]], ![![2, 0, 2], ![1, 0, 3], ![0, 0, 4], ![2, 1, 1], ![1, 1, 2], ![0, 1, 3]], ![![0, 2, 2], ![0, 1, 3], ![0, 0, 4], ![1, 2, 1], ![1, 1, 2], ![1, 0, 3]]]
def alphaCount : Fin 3 → Fin 6 → ℕ := ![![175650579516426, 317389560526428, 6960719833950, 6960811369144, 317389782454113, 175648546299939], ![175191304164176, 317540815868056, 7268782133764, 7268893245787, 317540995260535, 175189209327682], ![132856278741614, 167829593475912, 193650115724645, 193566698993678, 179087981733620, 133009331330531]]
def denominator : ℕ := 1999999999999998000000000000000000000000000000
def profileCount : Fin 12 → Fin 9 → ℕ :=
  ![![1999999999999998000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 75254572004245924745427995754000000000000000, 0, 1849490856006728150509143993270000000000000000, 0, 75254571989023924745428010976000000000000000, 0, 0], ![0, 0, 75254571989023924745428010976000000000000000, 0, 1849490856006728150509143993270000000000000000, 0, 75254572004245924745427995754000000000000000, 0, 0], ![0, 0, 0, 0, 0, 999999999999999000000000000000000000000000000, 0, 999999999999999000000000000000000000000000000, 0], ![0, 999999999999999000000000000000000000000000000, 0, 999999999999999000000000000000000000000000000, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1999999999999998000000000000000000000000000000], ![0, 0, 82066877672188036469111593136413219835891, 0, 1999835866244653623927061776813727173560328218, 0, 82066877672188036469111593136413219835891, 0, 0], ![0, 0, 41999999999999958000000000000000000000000000, 0, 1915999999999998084000000000000000000000000000, 0, 41999999999999958000000000000000000000000000, 0, 0], ![0, 0, 74068301837477925931698162522000000000000000, 0, 1851863395384538148136604615460000000000000000, 0, 74068302777981925931697222018000000000000000, 0, 0], ![0, 0, 74068302777981925931697222018000000000000000, 0, 1851863395384538148136604615460000000000000000, 0, 74068301837477925931698162522000000000000000, 0, 0], ![0, 0, 809323617663213190676382336786000000000000000, 0, 381352765438541618647234561458000000000000000, 0, 809323616898243190676383101756000000000000000, 0, 0], ![0, 0, 809323616898243190676383101756000000000000000, 0, 381352765438541618647234561458000000000000000, 0, 809323617663213190676382336786000000000000000, 0, 0]]
def profileIndex : Fin 6 → Fin 6 → Fin 3 → Fin 12 :=
  ![![![0, 1, 2], ![0, 3, 4], ![0, 5, 0], ![4, 4, 6], ![4, 7, 4], ![4, 3, 0]], ![![1, 0, 2], ![3, 0, 4], ![5, 0, 0], ![4, 4, 6], ![7, 4, 4], ![3, 4, 0]], ![![8, 9, 0], ![3, 4, 0], ![5, 0, 0], ![4, 7, 4], ![7, 4, 4], ![3, 0, 4]], ![![9, 8, 0], ![4, 3, 0], ![0, 5, 0], ![7, 4, 4], ![4, 7, 4], ![0, 3, 4]], ![![10, 0, 11], ![4, 0, 3], ![0, 0, 5], ![7, 4, 4], ![4, 4, 6], ![0, 4, 3]], ![![0, 10, 11], ![0, 4, 3], ![0, 0, 5], ![4, 7, 4], ![4, 4, 6], ![4, 0, 3]]]

def fineCount (r : Fin 6) (j : Fin 6) (i : Fin 3) (w : Fin 9) : ℕ :=
  profileCount (profileIndex r j i) w

def word : Fin 9 → CompleteSplit.CompleteWord 2 :=
  ![![0,0],![0,1],![0,2],![1,0],![1,1],![1,2],![2,0],![2,1],![2,2]]

/-- The nine actual two-letter words, in lexicographic order. -/
noncomputable def wordEquiv : Fin 9 ≃ CompleteSplit.CompleteWord 2 :=
  Equiv.ofBijective word (by decide +kernel)

/-- The eight admissible left-half grades in each physical orientation. -/
def splitMap (r : Fin 6) (j : Fin 6) : RecursiveThinSplit.Split 4 (parent r) :=
  ⟨shape r j, by
    have h : ∀ r j,
      (shape r j 0).val + (shape r j 1).val + (shape r j 2).val = 4 ∧
        ∀ i, (shape r j i).val ≤ parent r i := by decide +kernel
    exact h r j⟩

noncomputable def splitEquiv (r : Fin 6) : Fin 6 ≃ RecursiveThinSplit.Split 4 (parent r) :=
  Equiv.ofBijective (splitMap r) (by
    have h : ∀ r, Function.Bijective (splitMap r) := by decide +kernel
    exact h r)

theorem parent_total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * 4 := by decide +kernel

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent152.regionalWeight (region r)
def n (r : Fin 6) : ℕ := weightCount r * 1000000000000000 * denominator
noncomputable def m (r : Fin 6) (c : RecursiveThinSplit.Split 4 (parent r)) : ℕ :=
  weightCount r * alphaCount (region r) ((splitEquiv r).symm c) * denominator
noncomputable def mu (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteSplit.CompleteWord 2) : ℕ :=
  let j := (splitEquiv c.1).symm c.2
  weightCount c.1 * (alphaCount (region c.1) j + alphaCount (region c.1) (Fin.rev j)) *
    fineCount c.1 j i (wordEquiv.symm w)
def totalCount : ℕ := 1999999999999998000000000000000 * denominator

/-- Normalized formulas used to certify the entropy of the same integer data. -/
def weight (r : Fin 6) : ℚ := (weightCount r : ℚ) / 1999999999999998
def alpha (r : Fin 6) (j : Fin 6) : ℚ := (alphaCount (region r) j : ℚ) / 1000000000000000
def beta (r : Fin 6) (j : Fin 6) (i : Fin 3) (w : Fin 9) : ℚ :=
  (fineCount r j i w : ℚ) / denominator

def coarse (r : Fin 6) (i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ j : Fin 6, if shape r j i = g then alpha r j else 0

def jointWord (r : Fin 6) (i : Fin 3) (a b : Fin 9) : ℚ :=
  ∑ j : Fin 6, alpha r j * beta r j i a * beta r (Fin.rev j) i b

def boundary (i : Fin 2) (r : Fin 6) (j : Fin 6) : Bool :=
  if i = 0 then shape r j 2 = 0 else shape r j 0 = 0 ∨ shape r j 1 = 0

/-- Individual boundary parts 0..7 and grouped interior parts 8..12. -/
def partMass (i : Fin 2) (r : Fin 6) (s : Fin 11) (w : Fin 9) : ℚ :=
  ∑ j : Fin 6,
    if (if boundary i r j then j.val else 6 + (shape r j (yzMode i)).val) = s.val
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

end MME.DWZ152Fine


