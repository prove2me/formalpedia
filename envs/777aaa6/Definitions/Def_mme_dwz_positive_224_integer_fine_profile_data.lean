-- Prove2me | Definitions.Def_mme_dwz_positive_224_integer_fine_profile_data
-- name    : mme_dwz_positive_224_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T16:47:22.635202+00:00
-- url     : https://prove2.me/theorems/662e0d8c-51f3-4dd3-8b72-6a8b6c597133
-- title:
--   Concrete six-region integer fine profiles for the DWZ (2,2,4) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(2,2,4)$ component at $q=5$. It uses the published object-158 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 9 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here. For this non-thin component the coarse branch of `explicitRate` also subtracts `penaltyRate`: the weighted gap between the public recursive maximum-entropy upper bounds of the regional parents (`witnessIndex` into `mme_dwz_fourth_rational_recursive_entropy_data`) and the entropies of the actual split distributions.
-- source:
--   Released q=5 fourth-power certificate (object 158), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_224_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ224Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![2, 2, 4], ![2, 2, 4], ![2, 4, 2], ![4, 2, 2], ![4, 2, 2], ![2, 4, 2]]
def shape : Fin 6 → Fin 9 → Fin 3 → Fin 5 := ![![![0, 0, 4], ![0, 1, 3], ![0, 2, 2], ![1, 0, 3], ![1, 1, 2], ![1, 2, 1], ![2, 0, 2], ![2, 1, 1], ![2, 2, 0]], ![![0, 0, 4], ![1, 0, 3], ![2, 0, 2], ![0, 1, 3], ![1, 1, 2], ![2, 1, 1], ![0, 2, 2], ![1, 2, 1], ![2, 2, 0]], ![![0, 4, 0], ![1, 3, 0], ![2, 2, 0], ![0, 3, 1], ![1, 2, 1], ![2, 1, 1], ![0, 2, 2], ![1, 1, 2], ![2, 0, 2]], ![![4, 0, 0], ![3, 1, 0], ![2, 2, 0], ![3, 0, 1], ![2, 1, 1], ![1, 2, 1], ![2, 0, 2], ![1, 1, 2], ![0, 2, 2]], ![![4, 0, 0], ![3, 0, 1], ![2, 0, 2], ![3, 1, 0], ![2, 1, 1], ![1, 1, 2], ![2, 2, 0], ![1, 2, 1], ![0, 2, 2]], ![![0, 4, 0], ![0, 3, 1], ![0, 2, 2], ![1, 3, 0], ![1, 2, 1], ![1, 1, 2], ![2, 2, 0], ![2, 1, 1], ![2, 0, 2]]]
def alphaCount : Fin 3 → Fin 9 → ℕ := ![![15557611054, 36655880643410, 146527776735750, 36655873644212, 560289819753061, 36655881058102, 146527767117534, 36655885855074, 15557581803], ![15190643670, 34600677518190, 146670108750412, 36705083850414, 564017861764933, 36705090229500, 146670111823262, 34600684803511, 15190616108], ![137214782950802, 108794802411640, 93553758081497, 108067746505672, 103587915240302, 108915970642753, 94181508014911, 108488485218275, 137195030934148]]
def denominator : ℕ := 1999999999999998000000000000000000000000000000
def profileCount : Fin 12 → Fin 9 → ℕ :=
  ![![1999999999999998000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1999999999999998000000000000000000000000000000], ![0, 999999999999999000000000000000000000000000000, 0, 999999999999999000000000000000000000000000000, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 999999999999999000000000000000000000000000000, 0, 999999999999999000000000000000000000000000000, 0], ![0, 0, 86410876045809913589123954190000000000000000, 0, 1827178249061262172821750938736000000000000000, 0, 86410874892925913589125107074000000000000000, 0, 0], ![0, 0, 86410874892925913589125107074000000000000000, 0, 1827178249061262172821750938736000000000000000, 0, 86410876045809913589123954190000000000000000, 0, 0], ![0, 0, 11058207035607131065814321795979144484197841, 0, 1977883585928783737868371356408041711031604318, 0, 11058207035607131065814321795979144484197841, 0, 0], ![0, 0, 41999999999999958000000000000000000000000000, 0, 1915999999999998084000000000000000000000000000, 0, 41999999999999958000000000000000000000000000, 0, 0], ![0, 0, 110415205993823889584794006176000000000000000, 0, 1779169540906818220830459093180000000000000000, 0, 110415253099355889584746900644000000000000000, 0, 0], ![0, 0, 110415253099355889584746900644000000000000000, 0, 1779169540906818220830459093180000000000000000, 0, 110415205993823889584794006176000000000000000, 0, 0], ![0, 0, 74068301837477925931698162522000000000000000, 0, 1851863395384538148136604615460000000000000000, 0, 74068302777981925931697222018000000000000000, 0, 0], ![0, 0, 74068302777981925931697222018000000000000000, 0, 1851863395384538148136604615460000000000000000, 0, 74068301837477925931698162522000000000000000, 0, 0]]
def profileIndex : Fin 6 → Fin 9 → Fin 3 → Fin 12 :=
  ![![![0, 0, 1], ![0, 2, 3], ![0, 4, 5], ![2, 0, 3], ![2, 2, 6], ![2, 7, 2], ![8, 0, 9], ![7, 2, 2], ![10, 11, 0]], ![![0, 0, 1], ![2, 0, 3], ![4, 0, 5], ![0, 2, 3], ![2, 2, 6], ![7, 2, 2], ![0, 8, 9], ![2, 7, 2], ![11, 10, 0]], ![![0, 1, 0], ![2, 3, 0], ![10, 11, 0], ![0, 3, 2], ![2, 7, 2], ![7, 2, 2], ![0, 4, 5], ![2, 2, 6], ![8, 0, 9]], ![![1, 0, 0], ![3, 2, 0], ![11, 10, 0], ![3, 0, 2], ![7, 2, 2], ![2, 7, 2], ![4, 0, 5], ![2, 2, 6], ![0, 8, 9]], ![![1, 0, 0], ![3, 0, 2], ![8, 0, 9], ![3, 2, 0], ![7, 2, 2], ![2, 2, 6], ![10, 11, 0], ![2, 7, 2], ![0, 4, 5]], ![![0, 1, 0], ![0, 3, 2], ![0, 8, 9], ![2, 3, 0], ![2, 7, 2], ![2, 2, 6], ![11, 10, 0], ![7, 2, 2], ![4, 0, 5]]]

def fineCount (r : Fin 6) (j : Fin 9) (i : Fin 3) (w : Fin 9) : ℕ :=
  profileCount (profileIndex r j i) w

def word : Fin 9 → CompleteSplit.CompleteWord 2 :=
  ![![0,0],![0,1],![0,2],![1,0],![1,1],![1,2],![2,0],![2,1],![2,2]]

/-- The nine actual two-letter words, in lexicographic order. -/
noncomputable def wordEquiv : Fin 9 ≃ CompleteSplit.CompleteWord 2 :=
  Equiv.ofBijective word (by decide +kernel)

/-- The eight admissible left-half grades in each physical orientation. -/
def splitMap (r : Fin 6) (j : Fin 9) : RecursiveThinSplit.Split 4 (parent r) :=
  ⟨shape r j, by
    have h : ∀ r j,
      (shape r j 0).val + (shape r j 1).val + (shape r j 2).val = 4 ∧
        ∀ i, (shape r j i).val ≤ parent r i := by decide +kernel
    exact h r j⟩

noncomputable def splitEquiv (r : Fin 6) : Fin 9 ≃ RecursiveThinSplit.Split 4 (parent r) :=
  Equiv.ofBijective (splitMap r) (by
    have h : ∀ r, Function.Bijective (splitMap r) := by decide +kernel
    exact h r)

theorem parent_total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * 4 := by decide +kernel

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent224.regionalWeight (region r)
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
def alpha (r : Fin 6) (j : Fin 9) : ℚ := (alphaCount (region r) j : ℚ) / 1000000000000000
def beta (r : Fin 6) (j : Fin 9) (i : Fin 3) (w : Fin 9) : ℚ :=
  (fineCount r j i w : ℚ) / denominator

def coarse (r : Fin 6) (i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ j : Fin 9, if shape r j i = g then alpha r j else 0

def jointWord (r : Fin 6) (i : Fin 3) (a b : Fin 9) : ℚ :=
  ∑ j : Fin 9, alpha r j * beta r j i a * beta r (Fin.rev j) i b

def boundary (i : Fin 2) (r : Fin 6) (j : Fin 9) : Bool :=
  if i = 0 then shape r j 2 = 0 else shape r j 0 = 0 ∨ shape r j 1 = 0

/-- Individual boundary parts 0..7 and grouped interior parts 8..12. -/
def partMass (i : Fin 2) (r : Fin 6) (s : Fin 14) (w : Fin 9) : ℚ :=
  ∑ j : Fin 9,
    if (if boundary i r j then j.val else 9 + (shape r j (yzMode i)).val) = s.val
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
def witnessIndex : Fin 3 → Fin 63 := ![21, 22, 23]

/-- Witness maximum-entropy bound minus the split entropy, weighted over the six regions (nats). -/
noncomputable def penaltyRate : ℝ :=
  ∑ r, (weight r : ℝ) * (((DWZFourthRecursiveWitness.witness (witnessIndex (region r))).entropyUpper : ℝ) -
    ratEntropy (alpha r))

noncomputable def explicitRate : ℝ :=
  min (coarseRate - penaltyRate)
    (min (parentRate 1 - compatibilityRate 0) (parentRate 2 - compatibilityRate 1))

end MME.DWZ224Fine


