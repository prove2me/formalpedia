-- Prove2me | Definitions.Def_mme_dwz_positive_323_integer_fine_profile_data
-- name    : mme_dwz_positive_323_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T17:22:34.827999+00:00
-- url     : https://prove2.me/theorems/ec877bbf-e098-4710-94ab-207e63459e3d
-- title:
--   Concrete six-region integer fine profiles for the DWZ (3,2,3) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(3,2,3)$ component at $q=5$. It uses the published object-165 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 10 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here. For this non-thin component the coarse branch of `explicitRate` also subtracts `penaltyRate`: the weighted gap between the public recursive maximum-entropy upper bounds of the regional parents (`witnessIndex` into `mme_dwz_fourth_rational_recursive_entropy_data`) and the entropies of the actual split distributions.
-- source:
--   Released q=5 fourth-power certificate (object 165), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_323_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ323Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![3, 2, 3], ![2, 3, 3], ![2, 3, 3], ![3, 2, 3], ![3, 3, 2], ![3, 3, 2]]
def shape : Fin 6 → Fin 10 → Fin 3 → Fin 5 := ![![![0, 1, 3], ![0, 2, 2], ![1, 0, 3], ![1, 1, 2], ![1, 2, 1], ![2, 0, 2], ![2, 1, 1], ![2, 2, 0], ![3, 0, 1], ![3, 1, 0]], ![![1, 0, 3], ![2, 0, 2], ![0, 1, 3], ![1, 1, 2], ![2, 1, 1], ![0, 2, 2], ![1, 2, 1], ![2, 2, 0], ![0, 3, 1], ![1, 3, 0]], ![![1, 3, 0], ![2, 2, 0], ![0, 3, 1], ![1, 2, 1], ![2, 1, 1], ![0, 2, 2], ![1, 1, 2], ![2, 0, 2], ![0, 1, 3], ![1, 0, 3]], ![![3, 1, 0], ![2, 2, 0], ![3, 0, 1], ![2, 1, 1], ![1, 2, 1], ![2, 0, 2], ![1, 1, 2], ![0, 2, 2], ![1, 0, 3], ![0, 1, 3]], ![![3, 0, 1], ![2, 0, 2], ![3, 1, 0], ![2, 1, 1], ![1, 1, 2], ![2, 2, 0], ![1, 2, 1], ![0, 2, 2], ![1, 3, 0], ![0, 3, 1]], ![![0, 3, 1], ![0, 2, 2], ![1, 3, 0], ![1, 2, 1], ![1, 1, 2], ![2, 2, 0], ![2, 1, 1], ![2, 0, 2], ![3, 1, 0], ![3, 0, 1]]]
def alphaCount : Fin 3 → Fin 10 → ℕ := ![![106880520034518, 105124457511932, 103881986756077, 88816954781386, 94306894641695, 95188475481503, 88944273401248, 104619169223753, 105098732625342, 107138535542546], ![1656008381330, 11635250625344, 11454568081821, 315559466192277, 159694762686521, 159694873413568, 315559237481881, 11454582579210, 11635231551606, 1656019006442], ![1714937711693, 11529758590094, 11500795129509, 318117654697424, 157136912184138, 157137017814766, 318117415978138, 11500814566685, 11529755251805, 1714938075748]]
def denominator : ℕ := 999999999999999000000000000000000000000000000
def profileCount : Fin 11 → Fin 9 → ℕ :=
  ![![999999999999999000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 499999999999999500000000000000000000000000000, 0, 499999999999999500000000000000000000000000000, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 499999999999999500000000000000000000000000000, 0, 499999999999999500000000000000000000000000000, 0], ![0, 0, 52892834032856000000000000000000000000000000, 0, 894214128137930000000000000000000000000000000, 0, 52893037829213000000000000000000000000000000, 0, 0], ![0, 0, 52893037829213000000000000000000000000000000, 0, 894214128137930000000000000000000000000000000, 0, 52892834032856000000000000000000000000000000, 0, 0], ![0, 0, 5986906228341831139480568539124145309680757, 0, 988026187543315337721038862921751709380638486, 0, 5986906228341831139480568539124145309680757, 0, 0], ![0, 0, 20999999999999979000000000000000000000000000, 0, 957999999999999042000000000000000000000000000, 0, 20999999999999979000000000000000000000000000, 0, 0], ![0, 0, 57152326500067942847673499932000000000000000, 0, 885695321145250114304678854749000000000000000, 0, 57152352354680942847647645319000000000000000, 0, 0], ![0, 0, 57152352354680942847647645319000000000000000, 0, 885695321145250114304678854749000000000000000, 0, 57152326500067942847673499932000000000000000, 0, 0], ![0, 0, 37034150918738962965849081261000000000000000, 0, 925931697692269074068302307730000000000000000, 0, 37034151388990962965848611009000000000000000, 0, 0], ![0, 0, 37034151388990962965848611009000000000000000, 0, 925931697692269074068302307730000000000000000, 0, 37034150918738962965849081261000000000000000, 0, 0]]
def profileIndex : Fin 6 → Fin 10 → Fin 3 → Fin 11 :=
  ![![![0, 1, 2], ![0, 3, 4], ![1, 0, 2], ![1, 1, 5], ![1, 6, 1], ![7, 0, 8], ![6, 1, 1], ![9, 10, 0], ![2, 0, 1], ![2, 1, 0]], ![![1, 0, 2], ![3, 0, 4], ![0, 1, 2], ![1, 1, 5], ![6, 1, 1], ![0, 7, 8], ![1, 6, 1], ![10, 9, 0], ![0, 2, 1], ![1, 2, 0]], ![![1, 2, 0], ![9, 10, 0], ![0, 2, 1], ![1, 6, 1], ![6, 1, 1], ![0, 3, 4], ![1, 1, 5], ![7, 0, 8], ![0, 1, 2], ![1, 0, 2]], ![![2, 1, 0], ![10, 9, 0], ![2, 0, 1], ![6, 1, 1], ![1, 6, 1], ![3, 0, 4], ![1, 1, 5], ![0, 7, 8], ![1, 0, 2], ![0, 1, 2]], ![![2, 0, 1], ![7, 0, 8], ![2, 1, 0], ![6, 1, 1], ![1, 1, 5], ![9, 10, 0], ![1, 6, 1], ![0, 3, 4], ![1, 2, 0], ![0, 2, 1]], ![![0, 2, 1], ![0, 7, 8], ![1, 2, 0], ![1, 6, 1], ![1, 1, 5], ![10, 9, 0], ![6, 1, 1], ![3, 0, 4], ![2, 1, 0], ![2, 0, 1]]]

def fineCount (r : Fin 6) (j : Fin 10) (i : Fin 3) (w : Fin 9) : ℕ :=
  profileCount (profileIndex r j i) w

def word : Fin 9 → CompleteSplit.CompleteWord 2 :=
  ![![0,0],![0,1],![0,2],![1,0],![1,1],![1,2],![2,0],![2,1],![2,2]]

/-- The nine actual two-letter words, in lexicographic order. -/
noncomputable def wordEquiv : Fin 9 ≃ CompleteSplit.CompleteWord 2 :=
  Equiv.ofBijective word (by decide +kernel)

/-- The eight admissible left-half grades in each physical orientation. -/
def splitMap (r : Fin 6) (j : Fin 10) : RecursiveThinSplit.Split 4 (parent r) :=
  ⟨shape r j, by
    have h : ∀ r j,
      (shape r j 0).val + (shape r j 1).val + (shape r j 2).val = 4 ∧
        ∀ i, (shape r j i).val ≤ parent r i := by decide +kernel
    exact h r j⟩

noncomputable def splitEquiv (r : Fin 6) : Fin 10 ≃ RecursiveThinSplit.Split 4 (parent r) :=
  Equiv.ofBijective (splitMap r) (by
    have h : ∀ r, Function.Bijective (splitMap r) := by decide +kernel
    exact h r)

theorem parent_total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * 4 := by decide +kernel

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent323.regionalWeight (region r)
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
def alpha (r : Fin 6) (j : Fin 10) : ℚ := (alphaCount (region r) j : ℚ) / 1000000000000000
def beta (r : Fin 6) (j : Fin 10) (i : Fin 3) (w : Fin 9) : ℚ :=
  (fineCount r j i w : ℚ) / denominator

def coarse (r : Fin 6) (i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ j : Fin 10, if shape r j i = g then alpha r j else 0

def jointWord (r : Fin 6) (i : Fin 3) (a b : Fin 9) : ℚ :=
  ∑ j : Fin 10, alpha r j * beta r j i a * beta r (Fin.rev j) i b

def boundary (i : Fin 2) (r : Fin 6) (j : Fin 10) : Bool :=
  if i = 0 then shape r j 2 = 0 else shape r j 0 = 0 ∨ shape r j 1 = 0

/-- Individual boundary parts 0..7 and grouped interior parts 8..12. -/
def partMass (i : Fin 2) (r : Fin 6) (s : Fin 15) (w : Fin 9) : ℚ :=
  ∑ j : Fin 10,
    if (if boundary i r j then j.val else 10 + (shape r j (yzMode i)).val) = s.val
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
/-- Public recursive entropy witness of each of the three regional parents. -/
def witnessIndex : Fin 3 → Fin 63 := ![36, 37, 38]

/-- Witness maximum-entropy bound minus the split entropy, weighted over the six regions (nats). -/
noncomputable def penaltyRate : ℝ :=
  ∑ r, (weight r : ℝ) * (((DWZFourthRecursiveWitness.witness (witnessIndex (region r))).entropyUpper : ℝ) -
    ratEntropy (alpha r))

noncomputable def explicitRate : ℝ :=
  min (coarseRate - penaltyRate)
    (min (parentRate 1 - compatibilityRate 0) (parentRate 2 - compatibilityRate 1))

end MME.DWZ323Fine


