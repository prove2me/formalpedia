-- Prove2me | Definitions.Def_mme_dwz_positive_143_integer_fine_profile_data
-- name    : mme_dwz_positive_143_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T15:27:03.002331+00:00
-- url     : https://prove2.me/theorems/ffb3e82f-7b40-425d-b284-a9693e55d764
-- title:
--   Concrete six-region integer fine profiles for the DWZ (1,4,3) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(1,4,3)$ component at $q=5$. It uses the published object-152 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 8 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here.
-- source:
--   Released q=5 fourth-power certificate (object 152), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_143_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ143Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![1, 4, 3], ![4, 1, 3], ![4, 3, 1], ![3, 4, 1], ![3, 1, 4], ![1, 3, 4]]
def shape : Fin 6 → Fin 8 → Fin 3 → Fin 5 := ![![![0, 1, 3], ![0, 2, 2], ![0, 3, 1], ![0, 4, 0], ![1, 0, 3], ![1, 1, 2], ![1, 2, 1], ![1, 3, 0]], ![![1, 0, 3], ![2, 0, 2], ![3, 0, 1], ![4, 0, 0], ![0, 1, 3], ![1, 1, 2], ![2, 1, 1], ![3, 1, 0]], ![![1, 3, 0], ![2, 2, 0], ![3, 1, 0], ![4, 0, 0], ![0, 3, 1], ![1, 2, 1], ![2, 1, 1], ![3, 0, 1]], ![![3, 1, 0], ![2, 2, 0], ![1, 3, 0], ![0, 4, 0], ![3, 0, 1], ![2, 1, 1], ![1, 2, 1], ![0, 3, 1]], ![![3, 0, 1], ![2, 0, 2], ![1, 0, 3], ![0, 0, 4], ![3, 1, 0], ![2, 1, 1], ![1, 1, 2], ![0, 1, 3]], ![![0, 3, 1], ![0, 2, 2], ![0, 1, 3], ![0, 0, 4], ![1, 3, 0], ![1, 2, 1], ![1, 1, 2], ![1, 0, 3]]]
def alphaCount : Fin 3 → Fin 8 → ℕ := ![![12228287222828, 420824000056252, 66593365480538, 353276731704, 353270518225, 66592384500480, 420827279304096, 12228136185877], ![70864471524160, 250720888245013, 120525600399881, 57888438930106, 57888385898671, 120525289382969, 250722554068996, 70864371550204], ![13177281395473, 420200398411309, 66317945992176, 303276439765, 303270982118, 66317073269984, 420203625095134, 13177128414041]]
def denominator : ℕ := 999999999999999999999999999999000000000000000000000000000000
def profileCount : Fin 12 → Fin 9 → ℕ :=
  ![![999999999999999999999999999999000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 499999999999999999999999999999500000000000000000000000000000, 0, 499999999999999999999999999999500000000000000000000000000000, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 499999999999999999999999999999500000000000000000000000000000, 0, 499999999999999999999999999999500000000000000000000000000000, 0], ![0, 0, 39313745561813999999999999999960686254438186000000000000000, 0, 921372508914296999999999999999078627491085703000000000000000, 0, 39313745523888999999999999999960686254476111000000000000000, 0, 0], ![0, 0, 39313745523888999999999999999960686254476111000000000000000, 0, 921372508914296999999999999999078627491085703000000000000000, 0, 39313745561813999999999999999960686254438186000000000000000, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 999999999999999999999999999999000000000000000000000000000000], ![0, 0, 835920710211032084071418134214747385967677752332621903977, 0, 998328158579577935831857163730570505228064644495334756192046, 0, 835920710211032084071418134214747385967677752332621903977, 0, 0], ![0, 0, 20999999999999999999999999999979000000000000000000000000000, 0, 957999999999999999999999999999042000000000000000000000000000, 0, 20999999999999999999999999999979000000000000000000000000000, 0, 0], ![0, 0, 37034150918738999999999999999962965849081261000000000000000, 0, 925931697692269999999999999999074068302307730000000000000000, 0, 37034151388990999999999999999962965848611009000000000000000, 0, 0], ![0, 0, 37034151388990999999999999999962965848611009000000000000000, 0, 925931697692269999999999999999074068302307730000000000000000, 0, 37034150918738999999999999999962965849081261000000000000000, 0, 0], ![0, 0, 48188161086577048188161086577000000000000000000000000000000, 0, 903623678219867903623678219867000000000000000000000000000000, 0, 48188160693555048188160693555000000000000000000000000000000, 0, 0], ![0, 0, 48188160693555048188160693555000000000000000000000000000000, 0, 903623678219867903623678219867000000000000000000000000000000, 0, 48188161086577048188161086577000000000000000000000000000000, 0, 0]]
def profileIndex : Fin 6 → Fin 8 → Fin 3 → Fin 12 :=
  ![![![0, 1, 2], ![0, 3, 4], ![0, 2, 1], ![0, 5, 0], ![1, 0, 2], ![1, 1, 6], ![1, 7, 1], ![1, 2, 0]], ![![1, 0, 2], ![3, 0, 4], ![2, 0, 1], ![5, 0, 0], ![0, 1, 2], ![1, 1, 6], ![7, 1, 1], ![2, 1, 0]], ![![1, 2, 0], ![8, 9, 0], ![2, 1, 0], ![5, 0, 0], ![0, 2, 1], ![1, 7, 1], ![7, 1, 1], ![2, 0, 1]], ![![2, 1, 0], ![9, 8, 0], ![1, 2, 0], ![0, 5, 0], ![2, 0, 1], ![7, 1, 1], ![1, 7, 1], ![0, 2, 1]], ![![2, 0, 1], ![10, 0, 11], ![1, 0, 2], ![0, 0, 5], ![2, 1, 0], ![7, 1, 1], ![1, 1, 6], ![0, 1, 2]], ![![0, 2, 1], ![0, 10, 11], ![0, 1, 2], ![0, 0, 5], ![1, 2, 0], ![1, 7, 1], ![1, 1, 6], ![1, 0, 2]]]

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

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent143.regionalWeight (region r)
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

end MME.DWZ143Fine


