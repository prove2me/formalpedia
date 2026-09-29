-- Prove2me | Definitions.Def_Geometry_KernelPatterns_BellRecursion
-- name    : Geometry_KernelPatterns_BellRecursion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:37:37.392716+00:00
-- url     : https://prove2.me/theorems/cdb0b481-09c7-403f-86c4-ffc00d66396b
-- title:
--   Aether Catalog definitions — Geometry_KernelPatterns_BellRecursion
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KernelPatterns.BellRecursion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KernelPatterns/BellRecursion.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling

/-!
# Kernel patterns are counted by the Bell numbers, for every `n`

`Geometry.KernelPatterns.Bell` verified the first six values of the
pattern-counting sequence by `decide`.  Here we prove the general statement:

* `card_patterns_eq_bell` — `#(patterns n n) = Nat.bell n` for every `n`;
* `card_setoid_fin_eq_bell` — equivalently, the number of equivalence relations
  (set partitions) on an `n`-element set is `Nat.bell n`.

The proof runs the Bell recursion `B(n+1) = Σ_i C(n,i) B(n-i)` on the pattern
model.  A pattern of `Fin (n+1)` is split into

* the block `S` of the last index (a subset of `Fin n`), and
* the induced partition of the complement `Sᶜ`,

the second datum being encoded as an abstract `Setoid ↥Sᶜ`; the inverse
construction turns a setoid into a pattern by taking the kernel of the map
`blockFun` that collapses the last block to `none` and sends everything else to
its class.  Summing the fibre counts over all subsets `S` and grouping by
`|S|` produces exactly Mathlib's defining recursion for `Nat.bell`.
-/

namespace Geometry.KernelPatterns

open Finset

variable {n : ℕ}

attribute [local instance] Classical.propDecidable

/-! ### The last block of a pattern -/

/-- The part inside `Fin n` of the block of the last index. -/
def lastBlk (p : Fin (n + 1) → Fin (n + 1)) : Finset (Fin n) :=
  univ.filter fun i => p i.castSucc = p (Fin.last n)

@[simp] lemma mem_lastBlk {p : Fin (n + 1) → Fin (n + 1)} {i : Fin n} :
    i ∈ lastBlk p ↔ p i.castSucc = p (Fin.last n) := by
  simp [lastBlk]

/-! ### From a setoid on the complement back to a pattern -/

/-- Collapse the last block to `none`, and send every other index to its class
under `t`. -/
noncomputable def blockFun (S : Finset (Fin n)) (t : Setoid ↥(Sᶜ)) :
    Fin (n + 1) → Option (Quotient t) := fun a =>
  if h : (a : ℕ) < n then
    (if hs : (⟨a, h⟩ : Fin n) ∈ S then none
      else some (Quotient.mk t ⟨⟨a, h⟩, Finset.mem_compl.2 hs⟩))
  else none

@[simp] lemma blockFun_last (S : Finset (Fin n)) (t : Setoid ↥(Sᶜ)) :
    blockFun S t (Fin.last n) = none := by
  simp [blockFun]

lemma blockFun_castSucc_of_mem {S : Finset (Fin n)} (t : Setoid ↥(Sᶜ)) {i : Fin n}
    (hi : i ∈ S) : blockFun S t i.castSucc = none := by
  simp only [blockFun, Fin.val_castSucc, i.isLt, dif_pos]
  rw [dif_pos (by simpa using hi)]

lemma blockFun_castSucc_of_not_mem {S : Finset (Fin n)} (t : Setoid ↥(Sᶜ)) {i : Fin n}
    (hi : i ∉ S) :
    blockFun S t i.castSucc = some (Quotient.mk t ⟨i, Finset.mem_compl.2 hi⟩) := by
  simp only [blockFun, Fin.val_castSucc, i.isLt, dif_pos]
  rw [dif_neg (by simpa using hi)]

/-- The pattern attached to a subset together with a partition of its
complement. -/
noncomputable def patternOfSetoid (S : Finset (Fin n)) (t : Setoid ↥(Sᶜ)) :
    Fin (n + 1) → Fin (n + 1) :=
  pat (blockFun S t)

lemma patternOfSetoid_eq_iff (S : Finset (Fin n)) (t : Setoid ↥(Sᶜ)) (a b : Fin (n + 1)) :
    patternOfSetoid S t a = patternOfSetoid S t b ↔ blockFun S t a = blockFun S t b :=
  pat_eq_iff

lemma pat_patternOfSetoid (S : Finset (Fin n)) (t : Setoid ↥(Sᶜ)) :
    pat (patternOfSetoid S t) = patternOfSetoid S t :=
  pat_idem _

/-- Recognising `patternOfSetoid` by its kernel. -/
lemma patternOfSetoid_eq_of_kernel {S : Finset (Fin n)} {t : Setoid ↥(Sᶜ)}
    {p : Fin (n + 1) → Fin (n + 1)} (hpat : pat p = p)
    (h : ∀ a b, blockFun S t a = blockFun S t b ↔ p a = p b) :
    patternOfSetoid S t = p := by
  have : pat (blockFun S t) = pat p := pat_congr fun k l => h k l
  rw [patternOfSetoid, this, hpat]

lemma lastBlk_patternOfSetoid (S : Finset (Fin n)) (t : Setoid ↥(Sᶜ)) :
    lastBlk (patternOfSetoid S t) = S := by
  ext i
  rw [mem_lastBlk, patternOfSetoid_eq_iff, blockFun_last]
  constructor
  · intro h
    by_contra hi
    rw [blockFun_castSucc_of_not_mem t hi] at h
    simp at h
  · intro hi
    exact blockFun_castSucc_of_mem t hi

/-! ### The fibre of `lastBlk` over a subset -/

/-- The fibre: patterns of `Fin (n+1)` whose last block meets `Fin n` in `S`. -/
def lastBlkFibre (n : ℕ) (S : Finset (Fin n)) : Finset (Fin (n + 1) → Fin (n + 1)) :=
  (patterns (n + 1) (n + 1)).filter fun p => lastBlk p = S

lemma mem_lastBlkFibre {S : Finset (Fin n)} {p : Fin (n + 1) → Fin (n + 1)} :
    p ∈ lastBlkFibre n S ↔ pat p = p ∧ lastBlk p = S := by
  simp [lastBlkFibre, mem_patterns_self]

/-- **The fibre over `S` is the set of partitions of the complement of `S`.** -/
noncomputable def lastBlkFibreEquiv (n : ℕ) (S : Finset (Fin n)) :
    ↥(lastBlkFibre n S) ≃ Setoid ↥(Sᶜ) where
  toFun p := Setoid.ker fun x : ↥(Sᶜ) => (p : Fin (n + 1) → Fin (n + 1)) (x : Fin n).castSucc
  invFun t := ⟨patternOfSetoid S t, mem_lastBlkFibre.2
    ⟨pat_patternOfSetoid S t, lastBlk_patternOfSetoid S t⟩⟩
  left_inv := by
    rintro ⟨p, hp⟩
    obtain ⟨hpat, hblk⟩ := mem_lastBlkFibre.1 hp
    apply Subtype.ext
    show patternOfSetoid S _ = p
    set t : Setoid ↥(Sᶜ) := Setoid.ker fun x : ↥(Sᶜ) => p (x : Fin n).castSucc with ht
    have hkey : ∀ a b : Fin (n + 1), blockFun S t a = blockFun S t b ↔ p a = p b := by
      have hmemS : ∀ i : Fin n, i ∈ S ↔ p i.castSucc = p (Fin.last n) := by
        intro i; rw [← hblk, mem_lastBlk]
      intro a b
      rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨j, rfl⟩ | rfl
      · by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
        · rw [blockFun_castSucc_of_mem t hi, blockFun_castSucc_of_mem t hj]
          simp only [true_iff]
          rw [(hmemS i).1 hi, (hmemS j).1 hj]
        · rw [blockFun_castSucc_of_mem t hi, blockFun_castSucc_of_not_mem t hj]
          constructor
          · intro h; simp at h
          · intro h
            exact absurd ((hmemS j).2 (h ▸ (hmemS i).1 hi)) hj
        · rw [blockFun_castSucc_of_not_mem t hi, blockFun_castSucc_of_mem t hj]
          constructor
          · intro h; simp at h
          · intro h
            exact absurd ((hmemS i).2 (h.trans ((hmemS j).1 hj))) hi
        · rw [blockFun_castSucc_of_not_mem t hi, blockFun_castSucc_of_not_mem t hj]
          rw [Option.some_inj, Quotient.eq]
          exact Iff.rfl
      · by_cases hi : i ∈ S
        · rw [blockFun_castSucc_of_mem t hi, blockFun_last]
          simp only [true_iff]
          exact (hmemS i).1 hi
        · rw [blockFun_castSucc_of_not_mem t hi, blockFun_last]
          constructor
          · intro h; simp at h
          · intro h; exact absurd ((hmemS i).2 h) hi
      · by_cases hj : j ∈ S
        · rw [blockFun_castSucc_of_mem t hj, blockFun_last]
          simp only [true_iff]
          exact ((hmemS j).1 hj).symm
        · rw [blockFun_castSucc_of_not_mem t hj, blockFun_last]
          constructor
          · intro h; simp at h
          · intro h; exact absurd ((hmemS j).2 h.symm) hj
      · simp
    exact patternOfSetoid_eq_of_kernel hpat hkey
  right_inv := by
    intro t
    have hkey : ∀ x y : ↥(Sᶜ),
        patternOfSetoid S t (x : Fin n).castSucc = patternOfSetoid S t (y : Fin n).castSucc ↔
          Quotient.mk t x = Quotient.mk t y := by
      intro x y
      have hx : (x : Fin n) ∉ S := Finset.mem_compl.1 x.2
      have hy : (y : Fin n) ∉ S := Finset.mem_compl.1 y.2
      rw [patternOfSetoid_eq_iff, blockFun_castSucc_of_not_mem t hx,
        blockFun_castSucc_of_not_mem t hy, Option.some_inj]
    refine Setoid.ext fun x y => ?_
    show (patternOfSetoid S t (x : Fin n).castSucc = patternOfSetoid S t (y : Fin n).castSucc) ↔
      t.r x y
    rw [hkey x y, Quotient.eq]

/-! ### Counting -/

/-- Transport of the partition count along a bijection of index types. -/
noncomputable def setoidCongr {α β : Type*} (e : α ≃ β) : Setoid α ≃ Setoid β where
  toFun s := s.comap e.symm
  invFun s := s.comap e
  left_inv s := by
    refine Setoid.ext fun a b => ?_
    show s.r (e.symm (e a)) (e.symm (e b)) ↔ s.r a b
    simp
  right_inv s := by
    refine Setoid.ext fun a b => ?_
    show s.r (e (e.symm a)) (e (e.symm b)) ↔ s.r a b
    simp









end Geometry.KernelPatterns


