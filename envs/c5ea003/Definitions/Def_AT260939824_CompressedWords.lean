-- Prove2me | Definitions.Def_AT260939824_CompressedWords
-- name    : AT260939824_CompressedWords
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:41:12.802563+00:00
-- url     : https://prove2.me/theorems/d687d2b3-24b8-48e3-b2a6-2f07de7720de
-- title:
--   Compressed words and their group evaluation
-- statement:
--   For $m\ge2$ and $n\ge0$, a compressed word in letters $a,t,t^{-1}$ is defined by
--
--   $$ w_m(n)=\begin{cases}a^n,&n<m,\\ t\,w_m(\lfloor n/m\rfloor)\,t^{-1}a^{n\bmod m},&n\ge m.\end{cases} $$
--
--   Its length is at most $(m+1)(\lfloor\log_m n\rfloor+1)$, and the word for zero is empty. For any group and chosen elements $a,t$, word evaluation is the product of the corresponding letter values. It sends the empty word to the identity, concatenation to multiplication, and $n$ copies of the letter $a$ to $a^n$. These interfaces connect the compressed syntax with group-valued paths.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CompressedWords.lean, selected declaration lines 17-19, 21-24, 26-27, 29-30, 32-33, 35-37, 39-41, 43-48, 50-53, 55-57, 59-62, 91-115, 117-121; SHA-256 e6ee2a1004d8f2f06d31448a19671797dc2b032a3cec3bff24d8bd6626176d53. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
# Base-m compressed Baumslag--Solitar words

The words here are the actual recursive digit words used in Sections 4
and 7: `pₙ = t p_(n/m) t⁻¹ a^(n % m)`, with the bottom-digit case
`pₙ = aⁿ`. Their group value and explicit logarithmic edge-length bound
are proved from the single Baumslag--Solitar relation.
-/

namespace AbelianTargets

inductive BSLetter where
  | a | t | tInv
  deriving DecidableEq, Repr

def BSLetter.value {G : Type*} [Group G] (a t : G) : BSLetter → G
  | .a => a
  | .t => t
  | .tInv => t⁻¹

def bsWordValue {G : Type*} [Group G] (a t : G) (w : List BSLetter) : G :=
  (w.map (BSLetter.value a t)).prod

@[simp] theorem bsWordValue_nil {G : Type*} [Group G] (a t : G) :
    bsWordValue a t [] = 1 := rfl

@[simp] theorem bsWordValue_cons {G : Type*} [Group G] (a t : G) (s : BSLetter) (w : List BSLetter) :
    bsWordValue a t (s :: w) = s.value a t * bsWordValue a t w := rfl

@[simp] theorem bsWordValue_append {G : Type*} [Group G] (a t : G) (w z : List BSLetter) :
    bsWordValue a t (w ++ z) = bsWordValue a t w * bsWordValue a t z := by
  simp [bsWordValue]

@[simp] theorem bsWordValue_replicate_a {G : Type*} [Group G] (a t : G) (n : ℕ) :
    bsWordValue a t (List.replicate n BSLetter.a) = a ^ n := by
  simp [bsWordValue, BSLetter.value]

def compressedWord (m : ℕ) (hm : 2 ≤ m) (n : ℕ) : List BSLetter :=
  if _h : n < m then List.replicate n BSLetter.a
  else BSLetter.t :: (compressedWord m hm (n / m) ++
    BSLetter.tInv :: List.replicate (n % m) BSLetter.a)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

@[simp] theorem compressedWord_zero (m : ℕ) (hm : 2 ≤ m) :
    compressedWord m hm 0 = [] := by
  rw [compressedWord]
  simp only [show 0 < m by omega, dif_pos, List.replicate_zero]

theorem compressedWord_of_lt (m : ℕ) (hm : 2 ≤ m) {n : ℕ} (hn : n < m) :
    compressedWord m hm n = List.replicate n BSLetter.a := by
  rw [compressedWord, dif_pos hn]

theorem compressedWord_of_ge (m : ℕ) (hm : 2 ≤ m) {n : ℕ} (hn : m ≤ n) :
    compressedWord m hm n = BSLetter.t :: (compressedWord m hm (n / m) ++
      BSLetter.tInv :: List.replicate (n % m) BSLetter.a) := by
  rw [compressedWord, dif_neg (by omega)]





/-- A concrete version of the paper's `Oₘ(log(n+1))` edge bound. -/
theorem compressedWord_length_le (m : ℕ) (hm : 2 ≤ m) (n : ℕ) :
    (compressedWord m hm n).length ≤ (m + 1) * (Nat.log m n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < m
      · rw [compressedWord_of_lt m hm hn, List.length_replicate]
        calc
          n ≤ m + 1 := by omega
          _ = (m + 1) * 1 := by simp
          _ ≤ (m + 1) * (Nat.log m n + 1) :=
            Nat.mul_le_mul_left _ (by omega)
      · rw [compressedWord_of_ge m hm (by omega)]
        simp only [List.length_cons, List.length_append, List.length_replicate]
        have hq := ih (n/m) (Nat.div_lt_self (by omega) (by omega))
        have hlog : 1 ≤ Nat.log m n := by
          apply Nat.le_log_of_pow_le (by omega)
          simpa only [Nat.pow_one] using (show m ≤ n by omega)
        have hlogq : Nat.log m (n/m) + 1 = Nat.log m n := by
          rw [Nat.log_div_base]
          omega
        rw [hlogq] at hq
        have hmod := Nat.mod_lt n (show 0 < m by omega)
        rw [Nat.mul_add, Nat.mul_one]
        omega

theorem compressedWord_interval_uniform_length (m : ℕ) (hm : 2 ≤ m) (R n : ℕ)
    (hn : n ≤ R) :
    (compressedWord m hm n).length ≤ (m + 1) * (Nat.log m R + 1) :=
  (compressedWord_length_le m hm n).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right hn) 1))



end AbelianTargets


