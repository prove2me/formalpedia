-- Prove2me | Definitions.Def_mme_dwz_positive_521_integer_fine_profile_data
-- name    : mme_dwz_positive_521_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T16:46:56.980714+00:00
-- url     : https://prove2.me/theorems/bf4880ae-a8c3-4a8a-a655-25286763165b
-- title:
--   Concrete six-region integer fine profiles for the DWZ (5,2,1) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(5,2,1)$ component at $q=5$. It uses the published object-176 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 6 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here.
-- source:
--   Released q=5 fourth-power certificate (object 176), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_521_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ521Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![5, 2, 1], ![2, 5, 1], ![2, 1, 5], ![1, 2, 5], ![1, 5, 2], ![5, 1, 2]]
def shape : Fin 6 → Fin 6 → Fin 3 → Fin 5 := ![![![1, 2, 1], ![2, 1, 1], ![2, 2, 0], ![3, 0, 1], ![3, 1, 0], ![4, 0, 0]], ![![2, 1, 1], ![1, 2, 1], ![2, 2, 0], ![0, 3, 1], ![1, 3, 0], ![0, 4, 0]], ![![2, 1, 1], ![1, 1, 2], ![2, 0, 2], ![0, 1, 3], ![1, 0, 3], ![0, 0, 4]], ![![1, 2, 1], ![1, 1, 2], ![0, 2, 2], ![1, 0, 3], ![0, 1, 3], ![0, 0, 4]], ![![1, 1, 2], ![1, 2, 1], ![0, 2, 2], ![1, 3, 0], ![0, 3, 1], ![0, 4, 0]], ![![1, 1, 2], ![2, 1, 1], ![2, 0, 2], ![3, 1, 0], ![3, 0, 1], ![4, 0, 0]]]
def alphaCount : Fin 3 → Fin 6 → ℕ := ![![7263431674652, 317567646399836, 175168921925471, 175168921925613, 317567646399760, 7263431674668], ![162820928953832, 168587757840582, 168591316472181, 168591316472181, 168587757840582, 162820922420642], ![6977201405145, 317373804264594, 175648994330249, 175648994330223, 317373804264653, 6977201405136]]
def denominator : ℕ := 999999999999999999999999999999000000000000000
def profileCount : Fin 12 → Fin 9 → ℕ :=
  ![![0, 499999999999999999999999999999500000000000000, 0, 499999999999999999999999999999500000000000000, 0, 0, 0, 0, 0], ![0, 0, 20999999999999999999999999999979000000000000, 0, 957999999999999999999999999999042000000000000, 0, 20999999999999999999999999999979000000000000, 0, 0], ![0, 0, 37034150918738999999999999999962965849081261, 0, 925931697692269999999999999999074068302307730, 0, 37034151388990999999999999999962965848611009, 0, 0], ![0, 0, 37034151388990999999999999999962965848611009, 0, 925931697692269999999999999999074068302307730, 0, 37034150918738999999999999999962965849081261, 0, 0], ![999999999999999999999999999999000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 499999999999999999999999999999500000000000000, 0, 499999999999999999999999999999500000000000000, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 999999999999999999999999999999000000000000000], ![0, 0, 31895642893042145622130030673801724058237, 0, 999936208714213915708755739937652396551883526, 0, 31895642893042145622130030673801724058237, 0, 0], ![0, 0, 333333333177516999999999999999666666666822483, 0, 333333333644964999999999999999666666666355035, 0, 333333333177517999999999999999666666666822482, 0, 0], ![0, 0, 333333333177517999999999999999666666666822482, 0, 333333333644964999999999999999666666666355035, 0, 333333333177516999999999999999666666666822483, 0, 0], ![0, 0, 37630087765978999999999999999962369912234021, 0, 924739822340271999999999999999075260177659728, 0, 37630089893748999999999999999962369910106251, 0, 0], ![0, 0, 37630089893748999999999999999962369910106251, 0, 924739822340271999999999999999075260177659728, 0, 37630087765978999999999999999962369912234021, 0, 0]]
def profileIndex : Fin 6 → Fin 6 → Fin 3 → Fin 12 :=
  ![![![0, 1, 0], ![1, 0, 0], ![2, 3, 4], ![5, 4, 0], ![5, 0, 4], ![6, 4, 4]], ![![1, 0, 0], ![0, 1, 0], ![3, 2, 4], ![4, 5, 0], ![0, 5, 4], ![4, 6, 4]], ![![1, 0, 0], ![0, 0, 7], ![8, 4, 9], ![4, 0, 5], ![0, 4, 5], ![4, 4, 6]], ![![0, 1, 0], ![0, 0, 7], ![4, 8, 9], ![0, 4, 5], ![4, 0, 5], ![4, 4, 6]], ![![0, 0, 7], ![0, 1, 0], ![4, 10, 11], ![0, 5, 4], ![4, 5, 0], ![4, 6, 4]], ![![0, 0, 7], ![1, 0, 0], ![10, 4, 11], ![5, 0, 4], ![5, 4, 0], ![6, 4, 4]]]

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

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent521.regionalWeight (region r)
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

end MME.DWZ521Fine


