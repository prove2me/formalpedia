-- Prove2me | Definitions.Def_mme_dwz_positive_512_integer_fine_profile_data
-- name    : mme_dwz_positive_512_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T16:23:36.68815+00:00
-- url     : https://prove2.me/theorems/0718e869-2c83-419d-853a-db62501fda64
-- title:
--   Concrete six-region integer fine profiles for the DWZ (5,1,2) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(5,1,2)$ component at $q=5$. It uses the published object-175 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 6 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here.
-- source:
--   Released q=5 fourth-power certificate (object 175), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_512_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ512Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![5, 1, 2], ![1, 5, 2], ![1, 2, 5], ![2, 1, 5], ![2, 5, 1], ![5, 2, 1]]
def shape : Fin 6 → Fin 6 → Fin 3 → Fin 5 := ![![![1, 1, 2], ![2, 0, 2], ![2, 1, 1], ![3, 0, 1], ![3, 1, 0], ![4, 0, 0]], ![![1, 1, 2], ![0, 2, 2], ![1, 2, 1], ![0, 3, 1], ![1, 3, 0], ![0, 4, 0]], ![![1, 2, 1], ![0, 2, 2], ![1, 1, 2], ![0, 1, 3], ![1, 0, 3], ![0, 0, 4]], ![![2, 1, 1], ![2, 0, 2], ![1, 1, 2], ![1, 0, 3], ![0, 1, 3], ![0, 0, 4]], ![![2, 1, 1], ![2, 2, 0], ![1, 2, 1], ![1, 3, 0], ![0, 3, 1], ![0, 4, 0]], ![![1, 2, 1], ![2, 2, 0], ![2, 1, 1], ![3, 1, 0], ![3, 0, 1], ![4, 0, 0]]]
def alphaCount : Fin 3 → Fin 6 → ℕ := ![![6954373887403, 175631015427407, 317413922590377, 317414104963459, 175632162502153, 6954420629201], ![194554499512508, 131712009112378, 180864750896743, 166295222867294, 131940592460495, 194632925150582], ![7268774190332, 175167575571617, 317562946516879, 317563096458922, 175168764861635, 7268842400615]]
def denominator : ℕ := 181818181818182181818181818182000000000000000
def profileCount : Fin 12 → Fin 9 → ℕ :=
  ![![0, 90909090909091090909090909091000000000000000, 0, 90909090909091090909090909091000000000000000, 0, 0, 0, 0, 0], ![0, 0, 6993650832348162221243507473932285208705, 0, 181804194516517485493739331167052135429582590, 0, 6993650832348162221243507473932285208705, 0, 0], ![0, 0, 6841417540996013682835081992006841417540996, 0, 168135346747004699907057130372531771710383368, 0, 6841417530181468228289605817461386872075636, 0, 0], ![181818181818182181818181818182000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 6841417530181468228289605817461386872075636, 0, 168135346747004699907057130372531771710383368, 0, 6841417540996013682835081992006841417540996, 0, 0], ![0, 0, 3818181818181825818181818181822000000000000, 0, 174181818181818530181818181818356000000000000, 0, 3818181818181825818181818181822000000000000, 0, 0], ![0, 0, 0, 0, 0, 90909090909091090909090909091000000000000000, 0, 90909090909091090909090909091000000000000000, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 181818181818182181818181818182000000000000000], ![0, 0, 73714257809069420155788345411346441530536342, 0, 34389666665802614233878786150579844212120348, 0, 73714257343310147428514686620073714257343310, 0, 0], ![0, 0, 73714257343310147428514686620073714257343310, 0, 34389666665802614233878786150579844212120348, 0, 73714257809069420155788345411346441530536342, 0, 0], ![0, 0, 6733481985225286194236697723279460754712498, 0, 168351217762231245793344615371077442126853140, 0, 6733482070725649830600505087643097118434362, 0, 0], ![0, 0, 6733482070725649830600505087643097118434362, 0, 168351217762231245793344615371077442126853140, 0, 6733481985225286194236697723279460754712498, 0, 0]]
def profileIndex : Fin 6 → Fin 6 → Fin 3 → Fin 12 :=
  ![![![0, 0, 1], ![2, 3, 4], ![5, 0, 0], ![6, 3, 0], ![6, 0, 3], ![7, 3, 3]], ![![0, 0, 1], ![3, 2, 4], ![0, 5, 0], ![3, 6, 0], ![0, 6, 3], ![3, 7, 3]], ![![0, 5, 0], ![3, 8, 9], ![0, 0, 1], ![3, 0, 6], ![0, 3, 6], ![3, 3, 7]], ![![5, 0, 0], ![8, 3, 9], ![0, 0, 1], ![0, 3, 6], ![3, 0, 6], ![3, 3, 7]], ![![5, 0, 0], ![10, 11, 3], ![0, 5, 0], ![0, 6, 3], ![3, 6, 0], ![3, 7, 3]], ![![0, 5, 0], ![11, 10, 3], ![5, 0, 0], ![6, 0, 3], ![6, 3, 0], ![7, 3, 3]]]

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

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent512.regionalWeight (region r)
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

end MME.DWZ512Fine


