-- Prove2me | Definitions.Def_mme_dwz_positive_611_integer_fine_profile_data
-- name    : mme_dwz_positive_611_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T18:19:06.291411+00:00
-- url     : https://prove2.me/theorems/0b46619f-fb1b-4282-aefe-fb4de3584ba2
-- title:
--   Concrete four-region integer fine profiles for the DWZ (6,1,1) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(6,1,1)$ component at $q=5$. It uses the published object-179 regional weights and regional coarse distributions, in the two cyclic orientations of the regions with positive weight (the released weight of region 0 is zero), each paired with its X/Y swap. Each of the four physical regions has 4 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here.
-- source:
--   Released q=5 fourth-power certificate (object 179), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_611_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ611Fine

def region : Fin 4 → Fin 3 := ![0,0,1,1]
def keptMode : Fin 4 → Fin 3 := ![2,2,1,0]
def parent : Fin 4 → Fin 3 → ℕ := ![![6, 1, 1], ![1, 6, 1], ![1, 1, 6], ![1, 1, 6]]
def shape : Fin 4 → Fin 4 → Fin 3 → Fin 5 := ![![![2, 1, 1], ![3, 0, 1], ![3, 1, 0], ![4, 0, 0]], ![![1, 2, 1], ![0, 3, 1], ![1, 3, 0], ![0, 4, 0]], ![![1, 1, 2], ![0, 1, 3], ![1, 0, 3], ![0, 0, 4]], ![![1, 1, 2], ![1, 0, 3], ![0, 1, 3], ![0, 0, 4]]]
def alphaCount : Fin 3 → Fin 4 → ℕ := ![![118815454093260, 381184838164238, 381184982304641, 118814725437861], ![118814998606240, 381185001510602, 381185001633788, 118814998249370], ![259555472136481, 240444531761217, 240444531761217, 259555464341085]]
def denominator : ℕ := 1999999999999998000000000000000
def profileCount : Fin 6 → Fin 9 → ℕ :=
  ![![0, 0, 41999999999999958000000000000, 0, 1915999999999998084000000000000, 0, 41999999999999958000000000000, 0, 0], ![0, 999999999999999000000000000000, 0, 999999999999999000000000000000, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 999999999999999000000000000000, 0, 999999999999999000000000000000, 0], ![1999999999999998000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1999999999999998000000000000000], ![0, 0, 42582758524998623452417236977, 0, 1914834482950000753095165526046, 0, 42582758524998623452417236977, 0, 0]]
def profileIndex : Fin 4 → Fin 4 → Fin 3 → Fin 6 :=
  ![![![0, 1, 1], ![2, 3, 1], ![2, 1, 3], ![4, 3, 3]], ![![1, 0, 1], ![3, 2, 1], ![1, 2, 3], ![3, 4, 3]], ![![1, 1, 5], ![3, 1, 2], ![1, 3, 2], ![3, 3, 4]], ![![1, 1, 5], ![1, 3, 2], ![3, 1, 2], ![3, 3, 4]]]

def fineCount (r : Fin 4) (j : Fin 4) (i : Fin 3) (w : Fin 9) : ℕ :=
  profileCount (profileIndex r j i) w

def word : Fin 9 → CompleteSplit.CompleteWord 2 :=
  ![![0,0],![0,1],![0,2],![1,0],![1,1],![1,2],![2,0],![2,1],![2,2]]

/-- The nine actual two-letter words, in lexicographic order. -/
noncomputable def wordEquiv : Fin 9 ≃ CompleteSplit.CompleteWord 2 :=
  Equiv.ofBijective word (by decide +kernel)

/-- The eight admissible left-half grades in each physical orientation. -/
def splitMap (r : Fin 4) (j : Fin 4) : RecursiveThinSplit.Split 4 (parent r) :=
  ⟨shape r j, by
    have h : ∀ r j,
      (shape r j 0).val + (shape r j 1).val + (shape r j 2).val = 4 ∧
        ∀ i, (shape r j i).val ≤ parent r i := by decide +kernel
    exact h r j⟩

noncomputable def splitEquiv (r : Fin 4) : Fin 4 ≃ RecursiveThinSplit.Split 4 (parent r) :=
  Equiv.ofBijective (splitMap r) (by
    have h : ∀ r, Function.Bijective (splitMap r) := by decide +kernel
    exact h r)

theorem parent_total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * 4 := by decide +kernel

def weightCount (r : Fin 4) : ℕ := DWZPositiveComponent611.regionalWeight (region r)
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
def alpha (r : Fin 4) (j : Fin 4) : ℚ := (alphaCount (region r) j : ℚ) / 1000000000000000
def beta (r : Fin 4) (j : Fin 4) (i : Fin 3) (w : Fin 9) : ℚ :=
  (fineCount r j i w : ℚ) / denominator

def coarse (r : Fin 4) (i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ j : Fin 4, if shape r j i = g then alpha r j else 0

def jointWord (r : Fin 4) (i : Fin 3) (a b : Fin 9) : ℚ :=
  ∑ j : Fin 4, alpha r j * beta r j i a * beta r (Fin.rev j) i b

def boundary (i : Fin 2) (r : Fin 4) (j : Fin 4) : Bool :=
  if i = 0 then shape r j 2 = 0 else shape r j 0 = 0 ∨ shape r j 1 = 0

/-- Individual boundary parts 0..7 and grouped interior parts 8..12. -/
def partMass (i : Fin 2) (r : Fin 4) (s : Fin 9) (w : Fin 9) : ℚ :=
  ∑ j : Fin 4,
    if (if boundary i r j then j.val else 4 + (shape r j (yzMode i)).val) = s.val
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

end MME.DWZ611Fine


