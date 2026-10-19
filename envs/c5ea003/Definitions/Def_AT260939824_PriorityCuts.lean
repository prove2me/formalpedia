-- Prove2me | Definitions.Def_AT260939824_PriorityCuts
-- name    : AT260939824_PriorityCuts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:42:13.169986+00:00
-- url     : https://prove2.me/theorems/e8d263d5-06dd-464c-a634-e10582ce141e
-- title:
--   The finite-priority parallel-cut algorithm
-- statement:
--   A priority neighborhood assigns each point at most $P$ symmetric nearby points and a proper priority in $\{0,\ldots,P-1\}$. Given integer centers and a scale $L\ge32P$ with $P\ge1$, a finite iteration chooses two cuts at every point, processing priorities successively. After $P$ stages, cuts at distinct nearby points are separated by more than $\lfloor L/(16P)\rfloor$. The point set itself may be infinite.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/PriorityCuts.lean, selected declaration lines 17-22, 24, 26-29, 31-46, 48-55, 73-83, 85-104, 106-120, 122-145, 147-156; SHA-256 7a3c4814aee644341b01fa7dd62262569afb98cb0ad864cc85f71dab61a7841c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CovariantCuts
import Init
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# The finite-priority parallel-cut algorithm

The marker family may be infinite. Every point has at most `P` nearby
markers and a proper priority in `Fin P`. Processing those priorities
constructs both cuts, with exact side ranges and uniform separation from
all cuts of distinct nearby markers. Supplying the priorities and turning
the retained boxes into a rectangular CW atlas remain separate steps.
-/

namespace AbelianTargets

noncomputable section

structure PriorityNeighborhood (X : Type*) (P : ℕ) where
  nearby : X → Finset X
  bound : ∀ x,(nearby x).card ≤ P
  symmetric : ∀ x y,y ∈ nearby x → x ∈ nearby y
  priority : X → Fin P
  proper : ∀ x y,y ∈ nearby x → x ≠ y → priority x ≠ priority y

def cutSide (p : ℤ×ℤ) (b : Bool) : ℤ := if b then p.2 else p.1

def earlierPriorityCuts {X : Type*} {P : ℕ} (N : PriorityNeighborhood X P)
    (old : X → ℤ×ℤ) (n : ℕ) (x : X) : Finset ℤ :=
  ((N.nearby x).filter (fun y => (N.priority y).val < n)).biUnion
    (fun y => { (old y).1,(old y).2 })

theorem earlierPriorityCuts_card {X : Type*} {P : ℕ} (N : PriorityNeighborhood X P)
    (old : X → ℤ×ℤ) (n : ℕ) (x : X) :
    (earlierPriorityCuts N old n x).card ≤ 2*P := by
  classical
  unfold earlierPriorityCuts
  calc
    _ ≤ ∑ y ∈ (N.nearby x).filter (fun y => (N.priority y).val < n),
        ({(old y).1,(old y).2} : Finset ℤ).card := Finset.card_biUnion_le
    _ ≤ ∑ y ∈ (N.nearby x).filter (fun y => (N.priority y).val < n), 2 := by
      apply Finset.sum_le_sum
      intro y _
      exact (Finset.card_insert_le _ _).trans (by simp)
    _ = ((N.nearby x).filter (fun y => (N.priority y).val < n)).card * 2 := by
      simp [nsmul_eq_mul]
    _ ≤ P*2 := Nat.mul_le_mul_right 2 ((Finset.card_filter_le _ _).trans (N.bound x))
    _ = 2*P := Nat.mul_comm _ _

theorem cutSide_mem_earlierPriorityCuts {X : Type*} {P : ℕ} (N : PriorityNeighborhood X P)
    (old : X → ℤ×ℤ) (n : ℕ) {x y : X} (hy : y ∈ N.nearby x)
    (hprior : (N.priority y).val < n) (b : Bool) :
    cutSide (old y) b ∈ earlierPriorityCuts N old n x := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨y,Finset.mem_filter.mpr ⟨hy,hprior⟩,?_⟩
  cases b <;> simp [cutSide]



def priorityCutIteration {X : Type*} {P L : ℕ} (N : PriorityNeighborhood X P)
    (hP : 1 ≤ P) (hL : 32*P ≤ L) (center : X → ℤ) : ℕ → X → ℤ×ℤ
  | 0,x => (center x-3*L,center x+2*L)
  | n+1,x => if (N.priority x).val = n then
      (selectedCut hP hL (center x-3*L)
        (earlierPriorityCuts N (priorityCutIteration N hP hL center n) n x)
        (earlierPriorityCuts_card N _ n x),
       selectedCut hP hL (center x+2*L)
        (earlierPriorityCuts N (priorityCutIteration N hP hL center n) n x)
        (earlierPriorityCuts_card N _ n x))
    else priorityCutIteration N hP hL center n x

theorem priorityCutIteration_bounds {X : Type*} {P L : ℕ} (N : PriorityNeighborhood X P)
    (hP : 1 ≤ P) (hL : 32*P ≤ L) (center : X → ℤ) (n : ℕ) (x : X) :
    center x-3*L ≤ (priorityCutIteration N hP hL center n x).1 ∧
    (priorityCutIteration N hP hL center n x).1 ≤ center x-2*L ∧
    center x+2*L ≤ (priorityCutIteration N hP hL center n x).2 ∧
    (priorityCutIteration N hP hL center n x).2 ≤ center x+3*L := by
  induction n with
  | zero => simp [priorityCutIteration]; omega
  | succ n ih =>
      rw [priorityCutIteration]
      split_ifs
      · obtain ⟨hlo,hhi,_⟩ := selectedCut_spec hP hL (center x-3*L)
          (earlierPriorityCuts N (priorityCutIteration N hP hL center n) n x)
          (earlierPriorityCuts_card N _ n x)
        obtain ⟨hlo',hhi',_⟩ := selectedCut_spec hP hL (center x+2*L)
          (earlierPriorityCuts N (priorityCutIteration N hP hL center n) n x)
          (earlierPriorityCuts_card N _ n x)
        dsimp
        omega
      · exact ih

theorem priorityCutIteration_new_old_separated {X : Type*} {P L : ℕ}
    (N : PriorityNeighborhood X P) (hP : 1 ≤ P) (hL : 32*P ≤ L)
    (center : X → ℤ) (n : ℕ) {x y : X} (hy : y ∈ N.nearby x)
    (hx : (N.priority x).val = n) (hprior : (N.priority y).val < n)
    (a b : Bool) :
    ((L/(16*P) : ℕ) : ℤ) <
      |cutSide (priorityCutIteration N hP hL center (n+1) x) a-
        cutSide (priorityCutIteration N hP hL center (n+1) y) b| := by
  have hyne : (N.priority y).val ≠ n := by omega
  rw [priorityCutIteration,if_pos hx,priorityCutIteration,if_neg hyne]
  have hmem := cutSide_mem_earlierPriorityCuts N (priorityCutIteration N hP hL center n)
    n hy hprior b
  cases a
  · exact (selectedCut_spec hP hL (center x-3*L) _ (earlierPriorityCuts_card N _ n x)).2.2 _ hmem
  · exact (selectedCut_spec hP hL (center x+2*L) _ (earlierPriorityCuts_card N _ n x)).2.2 _ hmem

theorem priorityCutIteration_separated {X : Type*} {P L : ℕ}
    (N : PriorityNeighborhood X P) (hP : 1 ≤ P) (hL : 32*P ≤ L)
    (center : X → ℤ) (n : ℕ) :
    ∀ x y,y ∈ N.nearby x → x ≠ y → (N.priority x).val < n → (N.priority y).val < n →
      ∀ a b,((L/(16*P) : ℕ) : ℤ) <
        |cutSide (priorityCutIteration N hP hL center n x) a-
          cutSide (priorityCutIteration N hP hL center n y) b| := by
  induction n with
  | zero => intro x y hy hne hx; omega
  | succ n ih =>
      intro x y hy hne hx hy' a b
      by_cases hxn : (N.priority x).val = n
      · have hyn : (N.priority y).val ≠ n := by
          intro hyn
          exact N.proper x y hy hne (Fin.ext (hxn.trans hyn.symm))
        exact priorityCutIteration_new_old_separated N hP hL center n hy hxn (by omega) a b
      · have hxo : (N.priority x).val < n := by omega
        by_cases hyn : (N.priority y).val = n
        · have h := priorityCutIteration_new_old_separated N hP hL center n
            (N.symmetric x y hy) hyn hxo b a
          simpa only [abs_sub_comm] using h
        · have hyo : (N.priority y).val < n := by omega
          rw [priorityCutIteration,if_neg hxn,priorityCutIteration,if_neg hyn]
          exact ih x y hy hne hxo hyo a b

/-- All priorities are processed after exactly `P` stages. The marker
family itself need not be finite. -/
theorem priorityCuts_separated {X : Type*} {P L : ℕ}
    (N : PriorityNeighborhood X P) (hP : 1 ≤ P) (hL : 32*P ≤ L)
    (center : X → ℤ) {x y : X} (hy : y ∈ N.nearby x) (hne : x ≠ y) (a b : Bool) :
    ((L/(16*P) : ℕ) : ℤ) <
      |cutSide (priorityCutIteration N hP hL center P x) a-
        cutSide (priorityCutIteration N hP hL center P y) b| :=
  priorityCutIteration_separated N hP hL center P x y hy hne
    (N.priority x).isLt (N.priority y).isLt a b



end

end AbelianTargets


