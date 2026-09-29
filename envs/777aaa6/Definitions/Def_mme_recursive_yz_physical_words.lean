-- Prove2me | Definitions.Def_mme_recursive_yz_physical_words
-- name    : mme_recursive_yz_physical_words
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-12T10:13:30.872389+00:00
-- url     : https://prove2.me/theorems/7eca510e-58be-430e-a575-d78384fa8a06
-- title:
--   Both halves and joint parent words in recursive Y/Z filtering
-- statement:
--   A parent component has total grade twice the child grade. A left split $a$ determines the right split $\bar a=\mathrm{parent}-a$. Physical positions include both halves of every parent occurrence, and the cell map selects the actual split for that half. The Y boundary consists of cells with zero Z grade; the Z boundary consists of cells with zero X or zero Y grade. Mode grouping retains the parent component and that mode's child grade.
--
--   A parent fine word is the ordered pair of its two child fine words. Parent types prescribe joint counts of these ordered pairs within each fixed coarse-mode word. The accompanying shuffles permute parent occurrences within a component and carry both halves together. This preserves the joint information needed for the typical-word denominator in Claims 6.18--6.20.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 6.8, 6.10, 6.11 and Claims 6.18--6.20; https://arxiv.org/html/2404.16349v2#S6.SS3. These are exact finite-count formalizations; the paper writes normalized profiles and asymptotic entropy bounds.

import Definitions.Def_mme_recursive_yz_compatibility
import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_complete_split_profile_projection

open BigOperators
set_option autoImplicit false
namespace MME.RecursiveYZ

/-- Actual parent/component cells for a recursive splitting problem. -/
abbrev Cell (half R : ℕ) (parent : Fin R → Fin 3 → ℕ) :=
  (r : Fin R) × RecursiveThinSplit.Split half (parent r)

/-- Y compatibility fixes the cells with zero Z grade. -/
def yBoundary {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (c : Cell half R parent) : Prop := (c.2.val 2).val = 0

/-- Z compatibility fixes the cells with zero X or zero Y grade. -/
def zBoundary {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (c : Cell half R parent) : Prop := (c.2.val 0).val = 0 ∨ (c.2.val 1).val = 0

def modeGroup {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (i : Fin 3) (c : Cell half R parent) : Fin R × Fin (half + 1) :=
  (c.1,c.2.val i)

/-- Positions in both halves of every parent occurrence. -/
abbrev Position {R : ℕ} (n : Fin R → ℕ) := (r : Fin R) × (Fin (n r) × Fin 2)

/-- The physical left-half split words; definitionally the existing hash addresses. -/
abbrev Address (half R : ℕ) (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ) :=
  ∀ r, Fin (n r) → RecursiveThinSplit.Split half (parent r)

/-- The other half of an admissible split of a parent of total grade 2*half. -/
def complement {half : ℕ} {parent : Fin 3 → ℕ}
    (htotal : parent 0 + parent 1 + parent 2 = 2 * half)
    (a : RecursiveThinSplit.Split half parent) : RecursiveThinSplit.Split half parent := by
  have h0 := a.property.2 0
  have h1 := a.property.2 1
  have h2 := a.property.2 2
  have hs := a.property.1
  let v : Fin 3 → Fin (half + 1) := fun i ↦ ⟨parent i - (a.val i).val, by
    fin_cases i
    · change parent 0 - (a.val 0).val < half + 1
      omega
    · change parent 1 - (a.val 1).val < half + 1
      omega
    · change parent 2 - (a.val 2).val < half + 1
      omega⟩
  exact ⟨v, by change _ + _ + _ = _; dsimp [v]; omega,
    fun i ↦ Nat.sub_le _ _⟩

@[simp] theorem complement_complement {half : ℕ} {parent : Fin 3 → ℕ}
    (htotal : parent 0 + parent 1 + parent 2 = 2 * half)
    (a : RecursiveThinSplit.Split half parent) :
    complement htotal (complement htotal a) = a := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change parent i - (parent i - (a.val i).val) = (a.val i).val
  exact Nat.sub_sub_self (a.property.2 i)

/-- The actual cell of a position in either half of a recursive parent. -/
def fullCell {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (p : Position n) : Cell half R parent :=
  ⟨p.1, if p.2.2 = 0 then a p.1 p.2.1 else complement (htotal p.1) (a p.1 p.2.1)⟩

/-- The full parent fine word retains the joint information between both halves. -/
def parentWord {R : ℕ} {n : Fin R → ℕ} {W : Type*}
    (f : Position n → W) (r : Fin R) (t : Fin (n r)) : Fin 2 → W :=
  fun h ↦ f ⟨r,t,h⟩

/-- Exact parent-word types inside each fixed coarse mode word. The two halves
are kept jointly, rather than replaced by their separate marginals. -/
noncomputable def ParentType {half R : ℕ} {n : Fin R → ℕ} {W : Type*}
    (y : ∀ r, Fin (n r) → Fin (half + 1))
    (eta : Fin R → Fin (half + 1) → (Fin 2 → W) → ℕ)
    (f : Position n → W) : Prop :=
  ∀ r, Useful (y r) (eta r) (parentWord f r)

def shuffleAddress {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (sigma : ∀ r, Equiv.Perm (Fin (n r))) :
    Address half R parent n ≃ Address half R parent n where
  toFun a r t := a r (sigma r t)
  invFun a r t := a r ((sigma r).symm t)
  left_inv a := by funext r t; simp
  right_inv a := by funext r t; simp

def shufflePosition {R : ℕ} {n : Fin R → ℕ}
    (sigma : ∀ r, Equiv.Perm (Fin (n r))) : Position n ≃ Position n :=
  Equiv.sigmaCongrRight (fun r ↦ Equiv.prodCongr (sigma r) (Equiv.refl _))

end MME.RecursiveYZ


