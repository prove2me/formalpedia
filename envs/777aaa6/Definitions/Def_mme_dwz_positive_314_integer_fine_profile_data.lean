-- Prove2me | Definitions.Def_mme_dwz_positive_314_integer_fine_profile_data
-- name    : mme_dwz_positive_314_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T15:27:01.373293+00:00
-- url     : https://prove2.me/theorems/82f73358-e4b7-4245-a6ec-8231575e7cae
-- title:
--   Concrete six-region integer fine profiles for the DWZ (3,1,4) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(3,1,4)$ component at $q=5$. It uses the published object-164 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 8 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here.
-- source:
--   Released q=5 fourth-power certificate (object 164), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_314_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ314Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![3, 1, 4], ![1, 3, 4], ![1, 4, 3], ![4, 1, 3], ![4, 3, 1], ![3, 4, 1]]
def shape : Fin 6 → Fin 8 → Fin 3 → Fin 5 := ![![![0, 0, 4], ![0, 1, 3], ![1, 0, 3], ![1, 1, 2], ![2, 0, 2], ![2, 1, 1], ![3, 0, 1], ![3, 1, 0]], ![![0, 0, 4], ![1, 0, 3], ![0, 1, 3], ![1, 1, 2], ![0, 2, 2], ![1, 2, 1], ![0, 3, 1], ![1, 3, 0]], ![![0, 4, 0], ![1, 3, 0], ![0, 3, 1], ![1, 2, 1], ![0, 2, 2], ![1, 1, 2], ![0, 1, 3], ![1, 0, 3]], ![![4, 0, 0], ![3, 1, 0], ![3, 0, 1], ![2, 1, 1], ![2, 0, 2], ![1, 1, 2], ![1, 0, 3], ![0, 1, 3]], ![![4, 0, 0], ![3, 0, 1], ![3, 1, 0], ![2, 1, 1], ![2, 2, 0], ![1, 2, 1], ![1, 3, 0], ![0, 3, 1]], ![![0, 4, 0], ![0, 3, 1], ![1, 3, 0], ![1, 2, 1], ![2, 2, 0], ![2, 1, 1], ![3, 1, 0], ![3, 0, 1]]]
def alphaCount : Fin 3 → Fin 8 → ℕ := ![![15556088266, 13316836242895, 60622442257039, 426045170958063, 426045171460968, 60622431513715, 13316835417552, 15556061502], ![15294718550, 13575104237130, 56193677672983, 430215927938028, 430215929589476, 56193667842480, 13575103306070, 15294695283], ![145903502628345, 110700798820372, 119279550497454, 129179452561386, 119423527122419, 118920094117175, 110673139473848, 145919934779001]]
def denominator : ℕ := 2000000000000004000000000000002000000000000000
def profileCount : Fin 12 → Fin 9 → ℕ :=
  ![![2000000000000004000000000000002000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 2000000000000004000000000000002000000000000000], ![0, 1000000000000002000000000000001000000000000000, 0, 1000000000000002000000000000001000000000000000, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1000000000000002000000000000001000000000000000, 0, 1000000000000002000000000000001000000000000000, 0], ![0, 0, 1778757917322365343795136536034703857574065, 0, 1996442484165359269312409726929930592284851870, 0, 1778757917322365343795136536034703857574065, 0, 0], ![0, 0, 96346199104190192692398208380096346199104190, 0, 1807307598641217614615197282429807307598641214, 0, 96346202254596192692404509192096346202254596, 0, 0], ![0, 0, 96346202254596192692404509192096346202254596, 0, 1807307598641217614615197282429807307598641214, 0, 96346199104190192692398208380096346199104190, 0, 0], ![0, 0, 42000000000000084000000000000042000000000000, 0, 1916000000000003832000000000001916000000000000, 0, 42000000000000084000000000000042000000000000, 0, 0], ![0, 0, 77845860662706077845860662706000000000000000, 0, 1844308278420179844308278420178000000000000000, 0, 77845860917118077845860917118000000000000000, 0, 0], ![0, 0, 77845860917118077845860917118000000000000000, 0, 1844308278420179844308278420178000000000000000, 0, 77845860662706077845860662706000000000000000, 0, 0], ![0, 0, 74068301837478148136603674956074068301837478, 0, 1851863395384543703726790769081851863395384540, 0, 74068302777982148136605555964074068302777982, 0, 0], ![0, 0, 74068302777982148136605555964074068302777982, 0, 1851863395384543703726790769081851863395384540, 0, 74068301837478148136603674956074068301837478, 0, 0]]
def profileIndex : Fin 6 → Fin 8 → Fin 3 → Fin 12 :=
  ![![![0, 0, 1], ![0, 2, 3], ![2, 0, 3], ![2, 2, 4], ![5, 0, 6], ![7, 2, 2], ![3, 0, 2], ![3, 2, 0]], ![![0, 0, 1], ![2, 0, 3], ![0, 2, 3], ![2, 2, 4], ![0, 5, 6], ![2, 7, 2], ![0, 3, 2], ![2, 3, 0]], ![![0, 1, 0], ![2, 3, 0], ![0, 3, 2], ![2, 7, 2], ![0, 8, 9], ![2, 2, 4], ![0, 2, 3], ![2, 0, 3]], ![![1, 0, 0], ![3, 2, 0], ![3, 0, 2], ![7, 2, 2], ![8, 0, 9], ![2, 2, 4], ![2, 0, 3], ![0, 2, 3]], ![![1, 0, 0], ![3, 0, 2], ![3, 2, 0], ![7, 2, 2], ![10, 11, 0], ![2, 7, 2], ![2, 3, 0], ![0, 3, 2]], ![![0, 1, 0], ![0, 3, 2], ![2, 3, 0], ![2, 7, 2], ![11, 10, 0], ![7, 2, 2], ![3, 2, 0], ![3, 0, 2]]]

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

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent314.regionalWeight (region r)
def n (r : Fin 6) : ℕ := weightCount r * 1000000000000000 * denominator
noncomputable def m (r : Fin 6) (c : RecursiveThinSplit.Split 4 (parent r)) : ℕ :=
  weightCount r * alphaCount (region r) ((splitEquiv r).symm c) * denominator
noncomputable def mu (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteSplit.CompleteWord 2) : ℕ :=
  let j := (splitEquiv c.1).symm c.2
  weightCount c.1 * (alphaCount (region c.1) j + alphaCount (region c.1) (Fin.rev j)) *
    fineCount c.1 j i (wordEquiv.symm w)
def totalCount : ℕ := 2000000000000002000000000000000 * denominator

/-- Normalized formulas used to certify the entropy of the same integer data. -/
def weight (r : Fin 6) : ℚ := (weightCount r : ℚ) / 2000000000000002
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

end MME.DWZ314Fine


