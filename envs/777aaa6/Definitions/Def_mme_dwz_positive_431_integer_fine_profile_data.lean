-- Prove2me | Definitions.Def_mme_dwz_positive_431_integer_fine_profile_data
-- name    : mme_dwz_positive_431_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T16:48:56.030812+00:00
-- url     : https://prove2.me/theorems/acc48a25-8400-461a-90f4-bc2e30a136c3
-- title:
--   Concrete four-region integer fine profiles for the DWZ (4,3,1) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(4,3,1)$ component at $q=5$. It uses the published object-172 regional weights and regional coarse distributions, in the two cyclic orientations of the regions with positive weight (the released weight of region 0 is zero), each paired with its X/Y swap. Each of the four physical regions has 8 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here.
-- source:
--   Released q=5 fourth-power certificate (object 172), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_431_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ431Fine

def region : Fin 4 → Fin 3 := ![1,1,2,2]
def keptMode : Fin 4 → Fin 3 := ![1,0,0,1]
def parent : Fin 4 → Fin 3 → ℕ := ![![3, 1, 4], ![1, 3, 4], ![1, 4, 3], ![4, 1, 3]]
def shape : Fin 4 → Fin 8 → Fin 3 → Fin 5 := ![![![3, 1, 0], ![2, 1, 1], ![3, 0, 1], ![1, 1, 2], ![2, 0, 2], ![0, 1, 3], ![1, 0, 3], ![0, 0, 4]], ![![1, 3, 0], ![1, 2, 1], ![0, 3, 1], ![1, 1, 2], ![0, 2, 2], ![1, 0, 3], ![0, 1, 3], ![0, 0, 4]], ![![1, 0, 3], ![1, 1, 2], ![0, 1, 3], ![1, 2, 1], ![0, 2, 2], ![1, 3, 0], ![0, 3, 1], ![0, 4, 0]], ![![0, 1, 3], ![1, 1, 2], ![1, 0, 3], ![2, 1, 1], ![2, 0, 2], ![3, 1, 0], ![3, 0, 1], ![4, 0, 0]]]
def alphaCount : Fin 3 → Fin 8 → ℕ := ![![112766320013458, 127479103716983, 131489247690326, 128260531547840, 128264617441555, 131487972338220, 127492831339336, 112759375912282], ![300673728078, 65962163104377, 13434501778979, 420302661400755, 420302661365149, 13434501773503, 65962163121086, 300673728073], ![351146671659, 66420990687604, 12437171222858, 420790691417464, 420790691426987, 12437171223112, 66420990678633, 351146671683]]
def denominator : ℕ := 999999999999999000000000000000000000000000000
def profileCount : Fin 12 → Fin 9 → ℕ :=
  ![![999999999999999000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 499999999999999500000000000000000000000000000, 0, 499999999999999500000000000000000000000000000, 0], ![0, 499999999999999500000000000000000000000000000, 0, 499999999999999500000000000000000000000000000, 0, 0, 0, 0, 0], ![0, 0, 20999999999999979000000000000000000000000000, 0, 957999999999999042000000000000000000000000000, 0, 20999999999999979000000000000000000000000000, 0, 0], ![0, 0, 37034150918738962965849081261000000000000000, 0, 925931697692269074068302307730000000000000000, 0, 37034151388990962965848611009000000000000000, 0, 0], ![0, 0, 37034151388990962965848611009000000000000000, 0, 925931697692269074068302307730000000000000000, 0, 37034150918738962965849081261000000000000000, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 999999999999999000000000000000000000000000000], ![0, 0, 834143028120215122435127238463488443927221, 0, 998331713943758569755129745523073023112145558, 0, 834143028120215122435127238463488443927221, 0, 0], ![0, 0, 48188868490509951811131509490000000000000000, 0, 903622305780124096377694219875000000000000000, 0, 48188825729364951811174270635000000000000000, 0, 0], ![0, 0, 48188825729364951811174270635000000000000000, 0, 903622305780124096377694219875000000000000000, 0, 48188868490509951811131509490000000000000000, 0, 0], ![0, 0, 39309217390177960690782609822000000000000000, 0, 921381570625482078618429374517000000000000000, 0, 39309211984338960690788015661000000000000000, 0, 0], ![0, 0, 39309211984338960690788015661000000000000000, 0, 921381570625482078618429374517000000000000000, 0, 39309217390177960690782609822000000000000000, 0, 0]]
def profileIndex : Fin 4 → Fin 8 → Fin 3 → Fin 12 :=
  ![![![1, 2, 0], ![3, 2, 2], ![1, 0, 2], ![2, 2, 7], ![8, 0, 9], ![0, 2, 1], ![2, 0, 1], ![0, 0, 6]], ![![2, 1, 0], ![2, 3, 2], ![0, 1, 2], ![2, 2, 7], ![0, 8, 9], ![2, 0, 1], ![0, 2, 1], ![0, 0, 6]], ![![2, 0, 1], ![2, 2, 7], ![0, 2, 1], ![2, 3, 2], ![0, 10, 11], ![2, 1, 0], ![0, 1, 2], ![0, 6, 0]], ![![0, 2, 1], ![2, 2, 7], ![2, 0, 1], ![3, 2, 2], ![10, 0, 11], ![1, 2, 0], ![1, 0, 2], ![6, 0, 0]]]

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

def weightCount (r : Fin 4) : ℕ := DWZPositiveComponent431.regionalWeight (region r)
def n (r : Fin 4) : ℕ := weightCount r * 1000000000000000 * denominator
noncomputable def m (r : Fin 4) (c : RecursiveThinSplit.Split 4 (parent r)) : ℕ :=
  weightCount r * alphaCount (region r) ((splitEquiv r).symm c) * denominator
noncomputable def mu (i : Fin 3) (c : Cell 4 4 parent) (w : CompleteSplit.CompleteWord 2) : ℕ :=
  let j := (splitEquiv c.1).symm c.2
  weightCount c.1 * (alphaCount (region c.1) j + alphaCount (region c.1) (Fin.rev j)) *
    fineCount c.1 j i (wordEquiv.symm w)
def totalCount : ℕ := 2000000000000002000000000000000 * denominator

/-- Normalized formulas used to certify the entropy of the same integer data. -/
def weight (r : Fin 4) : ℚ := (weightCount r : ℚ) / 2000000000000002
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

end MME.DWZ431Fine


