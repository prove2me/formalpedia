-- Prove2me | Definitions.Def_mme_dwz_positive_242_integer_fine_profile_data
-- name    : mme_dwz_positive_242_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T16:53:37.199636+00:00
-- url     : https://prove2.me/theorems/552be653-ee6c-4c99-98a2-c1238fc76c15
-- title:
--   Concrete six-region integer fine profiles for the DWZ (2,4,2) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(2,4,2)$ component at $q=5$. It uses the published object-160 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 9 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here. For this non-thin component the coarse branch of `explicitRate` also subtracts `penaltyRate`: the weighted gap between the public recursive maximum-entropy upper bounds of the regional parents (`witnessIndex` into `mme_dwz_fourth_rational_recursive_entropy_data`) and the entropies of the actual split distributions.
-- source:
--   Released q=5 fourth-power certificate (object 160), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_242_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ242Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![2, 4, 2], ![4, 2, 2], ![4, 2, 2], ![2, 4, 2], ![2, 2, 4], ![2, 2, 4]]
def shape : Fin 6 → Fin 9 → Fin 3 → Fin 5 := ![![![0, 2, 2], ![0, 3, 1], ![0, 4, 0], ![1, 1, 2], ![1, 2, 1], ![1, 3, 0], ![2, 0, 2], ![2, 1, 1], ![2, 2, 0]], ![![2, 0, 2], ![3, 0, 1], ![4, 0, 0], ![1, 1, 2], ![2, 1, 1], ![3, 1, 0], ![0, 2, 2], ![1, 2, 1], ![2, 2, 0]], ![![2, 2, 0], ![3, 1, 0], ![4, 0, 0], ![1, 2, 1], ![2, 1, 1], ![3, 0, 1], ![0, 2, 2], ![1, 1, 2], ![2, 0, 2]], ![![2, 2, 0], ![1, 3, 0], ![0, 4, 0], ![2, 1, 1], ![1, 2, 1], ![0, 3, 1], ![2, 0, 2], ![1, 1, 2], ![0, 2, 2]], ![![2, 0, 2], ![1, 0, 3], ![0, 0, 4], ![2, 1, 1], ![1, 1, 2], ![0, 1, 3], ![2, 2, 0], ![1, 2, 1], ![0, 2, 2]], ![![0, 2, 2], ![0, 1, 3], ![0, 0, 4], ![1, 2, 1], ![1, 1, 2], ![1, 0, 3], ![2, 2, 0], ![2, 1, 1], ![2, 0, 2]]]
def alphaCount : Fin 3 → Fin 9 → ℕ := ![![92275279547270, 110006562161921, 135845745309395, 109972457611166, 103772854126041, 109999513096336, 135845739817106, 110033612912700, 92248235418065], ![142334828795616, 38468867934088, 335243331399, 40831511371845, 556058761299233, 40831603506832, 335242401590, 38468854036578, 142335087322819], ![142306228814012, 40623813020469, 341075660717, 40668986659518, 552119455123216, 40669077510635, 341074730426, 40623795939591, 142306492541416]]
def denominator : ℕ := 12987012987012999999999999999987012987012987000000000000000
def profileCount : Fin 12 → Fin 9 → ℕ :=
  ![![12987012987012999999999999999987012987012987000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 717735512171312406047200482999282264487828687593952799517, 0, 11551541969177712850243267878988448458030822287149756732121, 0, 717735505663974743709531637999282264494336025256290468362, 0, 0], ![0, 0, 717735505663974743709531637999282264494336025256290468362, 0, 11551541969177712850243267878988448458030822287149756732121, 0, 717735512171312406047200482999282264487828687593952799517, 0, 0], ![0, 0, 0, 0, 0, 6493506493506499999999999999993506493506493500000000000000, 0, 6493506493506499999999999999993506493506493500000000000000, 0], ![0, 6493506493506499999999999999993506493506493500000000000000, 0, 6493506493506499999999999999993506493506493500000000000000, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 12987012987012999999999999999987012987012987000000000000000], ![0, 0, 71225956979239000217369860625516278488916320454086237715, 0, 12844561073054521999565260278735980430035154359091827524570, 0, 71225956979239000217369860625516278488916320454086237715, 0, 0], ![0, 0, 272727272727272999999999999999727272727272727000000000000, 0, 12441558441558453999999999999987558441558441546000000000000, 0, 272727272727272999999999999999727272727272727000000000000, 0, 0], ![0, 0, 566075458012220779220779220778654703762767000000000000000, 0, 11854862075746545454545454545442690592469708000000000000000, 0, 566075453254233766233766233765667690780512000000000000000, 0, 0], ![0, 0, 566075453254233766233766233765667690780512000000000000000, 0, 11854862075746545454545454545442690592469708000000000000000, 0, 566075458012220779220779220778654703762767000000000000000, 0, 0], ![0, 0, 480962998944662818625336606999519037001055337181374663393, 0, 12025086983016505531580489509987974913016983494468419510490, 0, 480963005051831649794173882999519036994948168350205826117, 0, 0], ![0, 0, 480963005051831649794173882999519036994948168350205826117, 0, 12025086983016505531580489509987974913016983494468419510490, 0, 480962998944662818625336606999519037001055337181374663393, 0, 0]]
def profileIndex : Fin 6 → Fin 9 → Fin 3 → Fin 12 :=
  ![![![0, 1, 2], ![0, 3, 4], ![0, 5, 0], ![4, 4, 6], ![4, 7, 4], ![4, 3, 0], ![8, 0, 9], ![7, 4, 4], ![10, 11, 0]], ![![1, 0, 2], ![3, 0, 4], ![5, 0, 0], ![4, 4, 6], ![7, 4, 4], ![3, 4, 0], ![0, 8, 9], ![4, 7, 4], ![11, 10, 0]], ![![10, 11, 0], ![3, 4, 0], ![5, 0, 0], ![4, 7, 4], ![7, 4, 4], ![3, 0, 4], ![0, 1, 2], ![4, 4, 6], ![8, 0, 9]], ![![11, 10, 0], ![4, 3, 0], ![0, 5, 0], ![7, 4, 4], ![4, 7, 4], ![0, 3, 4], ![1, 0, 2], ![4, 4, 6], ![0, 8, 9]], ![![8, 0, 9], ![4, 0, 3], ![0, 0, 5], ![7, 4, 4], ![4, 4, 6], ![0, 4, 3], ![10, 11, 0], ![4, 7, 4], ![0, 1, 2]], ![![0, 8, 9], ![0, 4, 3], ![0, 0, 5], ![4, 7, 4], ![4, 4, 6], ![4, 0, 3], ![11, 10, 0], ![7, 4, 4], ![1, 0, 2]]]

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

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent242.regionalWeight (region r)
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
def witnessIndex : Fin 3 → Fin 63 := ![27, 28, 29]

/-- Witness maximum-entropy bound minus the split entropy, weighted over the six regions (nats). -/
noncomputable def penaltyRate : ℝ :=
  ∑ r, (weight r : ℝ) * (((DWZFourthRecursiveWitness.witness (witnessIndex (region r))).entropyUpper : ℝ) -
    ratEntropy (alpha r))

noncomputable def explicitRate : ℝ :=
  min (coarseRate - penaltyRate)
    (min (parentRate 1 - compatibilityRate 0) (parentRate 2 - compatibilityRate 1))

end MME.DWZ242Fine


