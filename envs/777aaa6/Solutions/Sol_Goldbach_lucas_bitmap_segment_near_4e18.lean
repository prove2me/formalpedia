-- Prove2me | solution 1 for Goldbach.lucas_bitmap_segment_near_4e18
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T01:11:51.522994+00:00
-- url     : https://prove2.me/submissions/ad8638f9-aa8e-4176-a8fb-cdbf8db6b093

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.BigOperators.Group.List.Defs

set_option autoImplicit false


namespace GoldbachCertificate

/-- A decidable primality test; certificate soundness is proved separately. -/
def primeCheck (p : ℕ) : Bool :=
  decide (2 ≤ p) &&
    (List.range (Nat.sqrt p + 1)).all (fun m => decide (m < 2 ∨ ¬ m ∣ p))

/-- A shared dictionary of prime values. Ordering improves lookup performance,
but is not required for soundness. -/
inductive PrimeTree where
  | empty
  | node (p : ℕ) (left right : PrimeTree)
  deriving DecidableEq

def PrimeTree.check : PrimeTree → Bool
  | .empty => true
  | .node p left right => primeCheck p && left.check && right.check

def PrimeTree.contains (n : ℕ) : PrimeTree → Bool
  | .empty => false
  | .node p left right =>
    if n = p then true else if n < p then left.contains n else right.contains n

/-- One literal prime pair for each consecutive even number, beginning at
`2 * first`. The left coordinate is bounded by `smallBound`. -/
def checkRows (first smallBound : ℕ) (tree : PrimeTree) : List (ℕ × ℕ) → Bool
  | [] => true
  | (p, q) :: rows =>
    tree.contains p && tree.contains q && decide (p ≤ smallBound) &&
      decide (p + q = 2 * first) && checkRows (first + 1) smallBound tree rows

end GoldbachCertificate



namespace GoldbachBitmapCertificate
open GoldbachCertificate

/-- Bit `i` records an odd prime with half-index `base + i`. -/
def primeBits (base : ℕ) : PrimeTree → ℕ
  | .empty => 0
  | .node p left right =>
    (if p % 2 = 1 ∧ base ≤ p / 2 then 1 <<< (p / 2 - base) else 0) |||
      primeBits base left ||| primeBits base right

/-- Every selected left summand is an odd checked prime within the bound. -/
def leftCheck (smallBound : ℕ) (tree : PrimeTree) (left : List ℕ) : Bool :=
  left.all (fun p => tree.contains p && decide (p % 2 = 1 ∧ p ≤ smallBound))

/-- For odd `p,q`, `(p+q)/2 = p/2 + q/2 + 1`. -/
def sumBits (right : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => (right <<< (p / 2 + 1)) ||| sumBits right ps

def intervalMask (first count : ℕ) : ℕ := ((1 <<< count) - 1) <<< first

def covers (base first count : ℕ) (tree : PrimeTree) (left : List ℕ) : Bool :=
  decide ((sumBits (primeBits base tree) left &&& intervalMask first count) =
    intervalMask first count)

end GoldbachBitmapCertificate




namespace GoldbachCertificate

private lemma primeCheck_spec (p : ℕ) : primeCheck p = true ↔ Nat.Prime p := by
  simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun m hm hms => ?_⟩
    exact (h m (by omega)).resolve_left (by omega)
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun m hm => ?_⟩
    by_cases hm2 : m < 2
    · exact Or.inl hm2
    · exact Or.inr (h m (by omega) (by omega))

private lemma PrimeTree.contains_prime (tree : PrimeTree) (n : ℕ)
    (hc : tree.check = true) (hn : tree.contains n = true) : Nat.Prime n := by
  induction tree with
  | empty => simp [PrimeTree.contains] at hn
  | node p left right ihl ihr =>
    simp only [PrimeTree.check, Bool.and_eq_true] at hc
    simp only [PrimeTree.contains] at hn
    split_ifs at hn with heq hlt
    · subst n
      exact (primeCheck_spec p).mp hc.1.1
    · exact ihl hc.1.2 hn
    · exact ihr hc.2 hn

end GoldbachCertificate

namespace GoldbachBitmapCertificate
open GoldbachCertificate

private lemma primeBits_sound (tree : PrimeTree) (base i : ℕ)
    (ht : tree.check = true) (hb : (primeBits base tree).testBit i = true) :
    ∃ q : ℕ, q.Prime ∧ q % 2 = 1 ∧ q / 2 = base + i := by
  induction tree with
  | empty => simp [primeBits] at hb
  | node p left right ihl ihr =>
    simp only [PrimeTree.check, Bool.and_eq_true] at ht
    simp only [primeBits, Nat.testBit_lor, Bool.or_eq_true] at hb
    rcases hb with (hb | hb) | hb
    · split_ifs at hb with hp
      · rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hb
        have hi : p / 2 - base = i := of_decide_eq_true hb
        exact ⟨p, (primeCheck_spec p).mp ht.1.1, hp.1, by omega⟩
      · simp at hb
    · exact ihl ht.1.2 hb
    · exact ihr ht.2 hb

private lemma sumBits_sound (left : List ℕ) (tree : PrimeTree)
    (ht : tree.check = true) (right smallBound i : ℕ)
    (hl : leftCheck smallBound tree left = true)
    (hb : (sumBits right left).testBit i = true) :
    ∃ p j : ℕ, p.Prime ∧ p % 2 = 1 ∧ p ≤ smallBound ∧
      right.testBit j = true ∧ i = j + p / 2 + 1 := by
  induction left with
  | nil => simp [sumBits] at hb
  | cons p ps ih =>
    simp only [leftCheck, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [sumBits, Nat.testBit_lor, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hb
      exact ⟨p, i - (p / 2 + 1), tree.contains_prime p ht hl.1.1,
        hl.1.2.1, hl.1.2.2, hb.2, by omega⟩
    · exact ih hl.2 hb

private lemma intervalMask_bit (first count i : ℕ) (hlo : first ≤ i)
    (hhi : i < first + count) : (intervalMask first count).testBit i = true := by
  simp only [intervalMask, Nat.testBit_shiftLeft, Nat.one_shiftLeft,
    Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq]
  omega

private lemma covers_bit (base first count i : ℕ) (tree : PrimeTree) (left : List ℕ)
    (hc : covers base first count tree left = true) (hlo : first ≤ i)
    (hhi : i < first + count) : (sumBits (primeBits base tree) left).testBit i = true := by
  have heq : (sumBits (primeBits base tree) left &&& intervalMask first count) =
      intervalMask first count := of_decide_eq_true hc
  have hb := congrArg (fun x : ℕ => x.testBit i) heq
  change (sumBits (primeBits base tree) left &&& intervalMask first count).testBit i =
    (intervalMask first count).testBit i at hb
  rw [Nat.testBit_land, intervalMask_bit first count i hlo hhi] at hb
  simpa using hb

private lemma block_sound (base first count smallBound : ℕ) (tree : PrimeTree)
    (left : List ℕ) (ht : tree.check = true)
    (hl : leftCheck smallBound tree left = true)
    (hc : covers base first count tree left = true)
    (n : ℕ) (hlo : 2 * (base + first) ≤ n)
    (hhi : n < 2 * (base + first + count)) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ smallBound ∧ n = p + q := by
  obtain ⟨k, hk⟩ := he
  have hi : first ≤ n / 2 - base := by omega
  have hi' : n / 2 - base < first + count := by omega
  have hb := covers_bit base first count (n / 2 - base) tree left hc hi hi'
  obtain ⟨p, j, hp, hpo, hpb, hj, heq⟩ :=
    sumBits_sound left tree ht (primeBits base tree) smallBound (n / 2 - base) hl hb
  obtain ⟨q, hq, hqo, hqj⟩ := primeBits_sound tree base j ht hj
  exact ⟨p, q, hp, hq, hpb, by omega⟩

end GoldbachBitmapCertificate


namespace GoldbachPrimalityCertificate

private lemma prime_mem_of_dvd_prod (factors : List ℕ)
    (hp : ∀ r ∈ factors, Nat.Prime r) (q : ℕ) (hq : Nat.Prime q)
    (hd : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil =>
    simp only [List.prod_nil] at hd
    exact (hq.not_dvd_one hd).elim
  | cons r rs ih =>
    simp only [List.prod_cons] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have hr := hp r (by simp)
      have heq : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp hd
      simp [heq]
    · exact List.mem_cons_of_mem r (ih (fun s hs => hp s (List.mem_cons_of_mem r hs)) hd)

end GoldbachPrimalityCertificate

private lemma lucas_from_prime_list (p : ℕ) (a : ZMod p) (factors : List ℕ)
    (hp : ∀ r ∈ factors, Nat.Prime r) (hprod : factors.prod = p - 1)
    (ha : a ^ (p - 1) = 1)
    (hd : ∀ r ∈ factors, a ^ ((p - 1) / r) ≠ 1) : Nat.Prime p := by
  apply lucas_primality p a ha
  intro q hq hqd
  have hmem : q ∈ factors := GoldbachPrimalityCertificate.prime_mem_of_dvd_prod factors hp q hq
    (by rwa [hprod])
  exact hd q hmem

namespace GoldbachLucasSegmentPrimes
private lemma prime_2 : Nat.Prime 2 := Nat.prime_two

private lemma prime_3 : Nat.Prime 3 := by
  apply lucas_from_prime_list 3 (2 : ZMod 3) [2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact prime_2
  · decide +kernel
  · change (2 : ZMod 3) ^ 2 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · change (2 : ZMod 3) ^ 1 ≠ 1
      reduce_mod_char
      decide

private lemma prime_5 : Nat.Prime 5 := by
  apply lucas_from_prime_list 5 (2 : ZMod 5) [2,2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_2
  · decide +kernel
  · change (2 : ZMod 5) ^ 4 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 5) ^ 2 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 5) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_7 : Nat.Prime 7 := by
  apply lucas_from_prime_list 7 (3 : ZMod 7) [2,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel
  · change (3 : ZMod 7) ^ 6 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (3 : ZMod 7) ^ 3 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 7) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_11 : Nat.Prime 11 := by
  apply lucas_from_prime_list 11 (2 : ZMod 11) [2,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel
  · change (2 : ZMod 11) ^ 10 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 11) ^ 5 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 11) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_13 : Nat.Prime 13 := by
  apply lucas_from_prime_list 13 (2 : ZMod 13) [2,2,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
  · decide +kernel
  · change (2 : ZMod 13) ^ 12 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 13) ^ 6 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 13) ^ 6 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 13) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_17 : Nat.Prime 17 := by
  apply lucas_from_prime_list 17 (3 : ZMod 17) [2,2,2,2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
  · decide +kernel
  · change (3 : ZMod 17) ^ 16 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17) ^ 8 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 17) ^ 8 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 17) ^ 8 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 17) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_19 : Nat.Prime 19 := by
  apply lucas_from_prime_list 19 (2 : ZMod 19) [2,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (2 : ZMod 19) ^ 18 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 19) ^ 9 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 19) ^ 6 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 19) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_23 : Nat.Prime 23 := by
  apply lucas_from_prime_list 23 (5 : ZMod 23) [2,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_11
  · decide +kernel
  · change (5 : ZMod 23) ^ 22 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 23) ^ 11 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 23) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_29 : Nat.Prime 29 := by
  apply lucas_from_prime_list 29 (2 : ZMod 29) [2,2,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 29) ^ 28 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 29) ^ 14 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 29) ^ 14 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 29) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_31 : Nat.Prime 31 := by
  apply lucas_from_prime_list 31 (3 : ZMod 31) [2,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (3 : ZMod 31) ^ 30 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 31) ^ 15 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 31) ^ 10 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 31) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_37 : Nat.Prime 37 := by
  apply lucas_from_prime_list 37 (2 : ZMod 37) [2,2,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (2 : ZMod 37) ^ 36 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37) ^ 18 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37) ^ 18 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37) ^ 12 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_41 : Nat.Prime 41 := by
  apply lucas_from_prime_list 41 (6 : ZMod 41) [2,2,2,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
  · decide +kernel
  · change (6 : ZMod 41) ^ 40 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 41) ^ 20 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 41) ^ 20 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 41) ^ 20 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 41) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_43 : Nat.Prime 43 := by
  apply lucas_from_prime_list 43 (3 : ZMod 43) [2,3,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel
  · change (3 : ZMod 43) ^ 42 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 43) ^ 21 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 43) ^ 14 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 43) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_47 : Nat.Prime 47 := by
  apply lucas_from_prime_list 47 (5 : ZMod 47) [2,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_23
  · decide +kernel
  · change (5 : ZMod 47) ^ 46 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 47) ^ 23 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 47) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_53 : Nat.Prime 53 := by
  apply lucas_from_prime_list 53 (2 : ZMod 53) [2,2,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_13
  · decide +kernel
  · change (2 : ZMod 53) ^ 52 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 53) ^ 26 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 53) ^ 26 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 53) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_59 : Nat.Prime 59 := by
  apply lucas_from_prime_list 59 (2 : ZMod 59) [2,29]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_29
  · decide +kernel
  · change (2 : ZMod 59) ^ 58 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 59) ^ 29 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 59) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_61 : Nat.Prime 61 := by
  apply lucas_from_prime_list 61 (2 : ZMod 61) [2,2,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (2 : ZMod 61) ^ 60 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61) ^ 30 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 61) ^ 30 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 61) ^ 20 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 61) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_67 : Nat.Prime 67 := by
  apply lucas_from_prime_list 67 (2 : ZMod 67) [2,3,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel
  · change (2 : ZMod 67) ^ 66 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 67) ^ 33 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 67) ^ 22 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 67) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_71 : Nat.Prime 71 := by
  apply lucas_from_prime_list 71 (7 : ZMod 71) [2,5,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel
  · change (7 : ZMod 71) ^ 70 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 71) ^ 35 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 71) ^ 14 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 71) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_73 : Nat.Prime 73 := by
  apply lucas_from_prime_list 73 (5 : ZMod 73) [2,2,2,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (5 : ZMod 73) ^ 72 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 73) ^ 36 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 73) ^ 36 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 73) ^ 36 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 73) ^ 24 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 73) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_79 : Nat.Prime 79 := by
  apply lucas_from_prime_list 79 (3 : ZMod 79) [2,3,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel
  · change (3 : ZMod 79) ^ 78 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 79) ^ 39 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 79) ^ 26 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 79) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_83 : Nat.Prime 83 := by
  apply lucas_from_prime_list 83 (2 : ZMod 83) [2,41]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_41
  · decide +kernel
  · change (2 : ZMod 83) ^ 82 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 83) ^ 41 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 83) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_89 : Nat.Prime 89 := by
  apply lucas_from_prime_list 89 (3 : ZMod 89) [2,2,2,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_11
  · decide +kernel
  · change (3 : ZMod 89) ^ 88 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 89) ^ 44 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 89) ^ 44 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 89) ^ 44 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 89) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_97 : Nat.Prime 97 := by
  apply lucas_from_prime_list 97 (5 : ZMod 97) [2,2,2,2,2,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
  · decide +kernel
  · change (5 : ZMod 97) ^ 96 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97) ^ 48 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 97) ^ 48 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 97) ^ 48 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 97) ^ 48 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 97) ^ 48 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 97) ^ 32 ≠ 1
      reduce_mod_char
      decide

private lemma prime_101 : Nat.Prime 101 := by
  apply lucas_from_prime_list 101 (2 : ZMod 101) [2,2,5,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
  · decide +kernel
  · change (2 : ZMod 101) ^ 100 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101) ^ 50 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 101) ^ 50 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 101) ^ 20 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 101) ^ 20 ≠ 1
      reduce_mod_char
      decide

private lemma prime_103 : Nat.Prime 103 := by
  apply lucas_from_prime_list 103 (5 : ZMod 103) [2,3,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel
  · change (5 : ZMod 103) ^ 102 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 103) ^ 51 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 103) ^ 34 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 103) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_107 : Nat.Prime 107 := by
  apply lucas_from_prime_list 107 (2 : ZMod 107) [2,53]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_53
  · decide +kernel
  · change (2 : ZMod 107) ^ 106 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 107) ^ 53 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 107) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_109 : Nat.Prime 109 := by
  apply lucas_from_prime_list 109 (6 : ZMod 109) [2,2,3,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (6 : ZMod 109) ^ 108 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 109) ^ 54 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 109) ^ 54 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 109) ^ 36 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 109) ^ 36 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 109) ^ 36 ≠ 1
      reduce_mod_char
      decide

private lemma prime_113 : Nat.Prime 113 := by
  apply lucas_from_prime_list 113 (3 : ZMod 113) [2,2,2,2,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
  · decide +kernel
  · change (3 : ZMod 113) ^ 112 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 113) ^ 56 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 113) ^ 56 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 113) ^ 56 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 113) ^ 56 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 113) ^ 16 ≠ 1
      reduce_mod_char
      decide

private lemma prime_127 : Nat.Prime 127 := by
  apply lucas_from_prime_list 127 (3 : ZMod 127) [2,3,3,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_7
  · decide +kernel
  · change (3 : ZMod 127) ^ 126 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 127) ^ 63 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 127) ^ 42 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 127) ^ 42 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 127) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_131 : Nat.Prime 131 := by
  apply lucas_from_prime_list 131 (2 : ZMod 131) [2,5,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel
  · change (2 : ZMod 131) ^ 130 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 131) ^ 65 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 131) ^ 26 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 131) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_137 : Nat.Prime 137 := by
  apply lucas_from_prime_list 137 (3 : ZMod 137) [2,2,2,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_17
  · decide +kernel
  · change (3 : ZMod 137) ^ 136 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 137) ^ 68 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 137) ^ 68 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 137) ^ 68 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 137) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_139 : Nat.Prime 139 := by
  apply lucas_from_prime_list 139 (2 : ZMod 139) [2,3,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel
  · change (2 : ZMod 139) ^ 138 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 139) ^ 69 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 139) ^ 46 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 139) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_149 : Nat.Prime 149 := by
  apply lucas_from_prime_list 149 (2 : ZMod 149) [2,2,37]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_37
  · decide +kernel
  · change (2 : ZMod 149) ^ 148 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 149) ^ 74 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 149) ^ 74 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 149) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_151 : Nat.Prime 151 := by
  apply lucas_from_prime_list 151 (6 : ZMod 151) [2,3,5,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5
  · decide +kernel
  · change (6 : ZMod 151) ^ 150 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 151) ^ 75 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 151) ^ 50 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 151) ^ 30 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 151) ^ 30 ≠ 1
      reduce_mod_char
      decide

private lemma prime_157 : Nat.Prime 157 := by
  apply lucas_from_prime_list 157 (5 : ZMod 157) [2,2,3,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel
  · change (5 : ZMod 157) ^ 156 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 157) ^ 78 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 157) ^ 78 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 157) ^ 52 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 157) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_163 : Nat.Prime 163 := by
  apply lucas_from_prime_list 163 (2 : ZMod 163) [2,3,3,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (2 : ZMod 163) ^ 162 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 163) ^ 81 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 163) ^ 54 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 163) ^ 54 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 163) ^ 54 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 163) ^ 54 ≠ 1
      reduce_mod_char
      decide

private lemma prime_167 : Nat.Prime 167 := by
  apply lucas_from_prime_list 167 (5 : ZMod 167) [2,83]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_83
  · decide +kernel
  · change (5 : ZMod 167) ^ 166 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 167) ^ 83 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 167) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_173 : Nat.Prime 173 := by
  apply lucas_from_prime_list 173 (2 : ZMod 173) [2,2,43]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_43
  · decide +kernel
  · change (2 : ZMod 173) ^ 172 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 173) ^ 86 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 173) ^ 86 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 173) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_179 : Nat.Prime 179 := by
  apply lucas_from_prime_list 179 (2 : ZMod 179) [2,89]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_89
  · decide +kernel
  · change (2 : ZMod 179) ^ 178 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 179) ^ 89 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 179) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_181 : Nat.Prime 181 := by
  apply lucas_from_prime_list 181 (2 : ZMod 181) [2,2,3,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (2 : ZMod 181) ^ 180 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 181) ^ 90 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 181) ^ 90 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 181) ^ 60 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 181) ^ 60 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 181) ^ 36 ≠ 1
      reduce_mod_char
      decide

private lemma prime_191 : Nat.Prime 191 := by
  apply lucas_from_prime_list 191 (19 : ZMod 191) [2,5,19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel
  · change (19 : ZMod 191) ^ 190 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (19 : ZMod 191) ^ 95 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 191) ^ 38 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 191) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_193 : Nat.Prime 193 := by
  apply lucas_from_prime_list 193 (5 : ZMod 193) [2,2,2,2,2,2,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
  · decide +kernel
  · change (5 : ZMod 193) ^ 192 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 64 ≠ 1
      reduce_mod_char
      decide

private lemma prime_197 : Nat.Prime 197 := by
  apply lucas_from_prime_list 197 (2 : ZMod 197) [2,2,7,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 197) ^ 196 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 197) ^ 98 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 197) ^ 98 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 197) ^ 28 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 197) ^ 28 ≠ 1
      reduce_mod_char
      decide

private lemma prime_199 : Nat.Prime 199 := by
  apply lucas_from_prime_list 199 (3 : ZMod 199) [2,3,3,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_11
  · decide +kernel
  · change (3 : ZMod 199) ^ 198 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 199) ^ 99 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 199) ^ 66 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 199) ^ 66 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 199) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_211 : Nat.Prime 211 := by
  apply lucas_from_prime_list 211 (2 : ZMod 211) [2,3,5,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 211) ^ 210 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 211) ^ 105 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 211) ^ 70 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 211) ^ 42 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 211) ^ 30 ≠ 1
      reduce_mod_char
      decide

private lemma prime_223 : Nat.Prime 223 := by
  apply lucas_from_prime_list 223 (3 : ZMod 223) [2,3,37]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
  · decide +kernel
  · change (3 : ZMod 223) ^ 222 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 223) ^ 111 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 223) ^ 74 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 223) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_227 : Nat.Prime 227 := by
  apply lucas_from_prime_list 227 (2 : ZMod 227) [2,113]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_113
  · decide +kernel
  · change (2 : ZMod 227) ^ 226 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 227) ^ 113 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 227) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_229 : Nat.Prime 229 := by
  apply lucas_from_prime_list 229 (6 : ZMod 229) [2,2,3,19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel
  · change (6 : ZMod 229) ^ 228 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 229) ^ 114 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 229) ^ 114 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 229) ^ 76 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 229) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_233 : Nat.Prime 233 := by
  apply lucas_from_prime_list 233 (3 : ZMod 233) [2,2,2,29]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_29
  · decide +kernel
  · change (3 : ZMod 233) ^ 232 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 233) ^ 116 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 233) ^ 116 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 233) ^ 116 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 233) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_239 : Nat.Prime 239 := by
  apply lucas_from_prime_list 239 (7 : ZMod 239) [2,7,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
  · decide +kernel
  · change (7 : ZMod 239) ^ 238 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 239) ^ 119 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 239) ^ 34 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 239) ^ 14 ≠ 1
      reduce_mod_char
      decide

private lemma prime_241 : Nat.Prime 241 := by
  apply lucas_from_prime_list 241 (7 : ZMod 241) [2,2,2,2,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (7 : ZMod 241) ^ 240 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 241) ^ 120 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 241) ^ 120 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 241) ^ 120 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 241) ^ 120 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 241) ^ 80 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 241) ^ 48 ≠ 1
      reduce_mod_char
      decide

private lemma prime_251 : Nat.Prime 251 := by
  apply lucas_from_prime_list 251 (6 : ZMod 251) [2,5,5,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_5
  · decide +kernel
  · change (6 : ZMod 251) ^ 250 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 251) ^ 125 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 251) ^ 50 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 251) ^ 50 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 251) ^ 50 ≠ 1
      reduce_mod_char
      decide

private lemma prime_257 : Nat.Prime 257 := by
  apply lucas_from_prime_list 257 (3 : ZMod 257) [2,2,2,2,2,2,2,2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
  · decide +kernel
  · change (3 : ZMod 257) ^ 256 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide

private lemma prime_263 : Nat.Prime 263 := by
  apply lucas_from_prime_list 263 (5 : ZMod 263) [2,131]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_131
  · decide +kernel
  · change (5 : ZMod 263) ^ 262 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 263) ^ 131 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 263) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_269 : Nat.Prime 269 := by
  apply lucas_from_prime_list 269 (2 : ZMod 269) [2,2,67]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_67
  · decide +kernel
  · change (2 : ZMod 269) ^ 268 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 269) ^ 134 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 269) ^ 134 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 269) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_271 : Nat.Prime 271 := by
  apply lucas_from_prime_list 271 (6 : ZMod 271) [2,3,3,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (6 : ZMod 271) ^ 270 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 271) ^ 135 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 271) ^ 90 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 271) ^ 90 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 271) ^ 90 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 271) ^ 54 ≠ 1
      reduce_mod_char
      decide

private lemma prime_277 : Nat.Prime 277 := by
  apply lucas_from_prime_list 277 (5 : ZMod 277) [2,2,3,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel
  · change (5 : ZMod 277) ^ 276 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 277) ^ 138 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 277) ^ 138 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 277) ^ 92 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 277) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_281 : Nat.Prime 281 := by
  apply lucas_from_prime_list 281 (3 : ZMod 281) [2,2,2,5,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel
  · change (3 : ZMod 281) ^ 280 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 281) ^ 140 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 281) ^ 140 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 281) ^ 140 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 281) ^ 56 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 281) ^ 40 ≠ 1
      reduce_mod_char
      decide

private lemma prime_283 : Nat.Prime 283 := by
  apply lucas_from_prime_list 283 (3 : ZMod 283) [2,3,47]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel
  · change (3 : ZMod 283) ^ 282 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 283) ^ 141 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 283) ^ 94 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 283) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_293 : Nat.Prime 293 := by
  apply lucas_from_prime_list 293 (2 : ZMod 293) [2,2,73]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_73
  · decide +kernel
  · change (2 : ZMod 293) ^ 292 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 293) ^ 146 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 293) ^ 146 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 293) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_307 : Nat.Prime 307 := by
  apply lucas_from_prime_list 307 (5 : ZMod 307) [2,3,3,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_17
  · decide +kernel
  · change (5 : ZMod 307) ^ 306 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 307) ^ 153 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 307) ^ 102 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 307) ^ 102 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 307) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_313 : Nat.Prime 313 := by
  apply lucas_from_prime_list 313 (10 : ZMod 313) [2,2,2,3,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel
  · change (10 : ZMod 313) ^ 312 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 313) ^ 156 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 313) ^ 156 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 313) ^ 156 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 313) ^ 104 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 313) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_317 : Nat.Prime 317 := by
  apply lucas_from_prime_list 317 (2 : ZMod 317) [2,2,79]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_79
  · decide +kernel
  · change (2 : ZMod 317) ^ 316 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 317) ^ 158 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 317) ^ 158 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 317) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_331 : Nat.Prime 331 := by
  apply lucas_from_prime_list 331 (3 : ZMod 331) [2,3,5,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel
  · change (3 : ZMod 331) ^ 330 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 331) ^ 165 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 331) ^ 110 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 331) ^ 66 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 331) ^ 30 ≠ 1
      reduce_mod_char
      decide

private lemma prime_337 : Nat.Prime 337 := by
  apply lucas_from_prime_list 337 (10 : ZMod 337) [2,2,2,2,3,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel
  · change (10 : ZMod 337) ^ 336 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 337) ^ 168 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 337) ^ 168 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 337) ^ 168 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 337) ^ 168 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 337) ^ 112 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 337) ^ 48 ≠ 1
      reduce_mod_char
      decide

private lemma prime_347 : Nat.Prime 347 := by
  apply lucas_from_prime_list 347 (2 : ZMod 347) [2,173]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_173
  · decide +kernel
  · change (2 : ZMod 347) ^ 346 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 347) ^ 173 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 347) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_349 : Nat.Prime 349 := by
  apply lucas_from_prime_list 349 (2 : ZMod 349) [2,2,3,29]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel
  · change (2 : ZMod 349) ^ 348 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 349) ^ 174 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 349) ^ 174 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 349) ^ 116 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 349) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_353 : Nat.Prime 353 := by
  apply lucas_from_prime_list 353 (3 : ZMod 353) [2,2,2,2,2,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_11
  · decide +kernel
  · change (3 : ZMod 353) ^ 352 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 353) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 353) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 353) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 353) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 353) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 353) ^ 32 ≠ 1
      reduce_mod_char
      decide

private lemma prime_359 : Nat.Prime 359 := by
  apply lucas_from_prime_list 359 (7 : ZMod 359) [2,179]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_179
  · decide +kernel
  · change (7 : ZMod 359) ^ 358 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (7 : ZMod 359) ^ 179 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 359) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_367 : Nat.Prime 367 := by
  apply lucas_from_prime_list 367 (6 : ZMod 367) [2,3,61]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
  · decide +kernel
  · change (6 : ZMod 367) ^ 366 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (6 : ZMod 367) ^ 183 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 367) ^ 122 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 367) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_373 : Nat.Prime 373 := by
  apply lucas_from_prime_list 373 (2 : ZMod 373) [2,2,3,31]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel
  · change (2 : ZMod 373) ^ 372 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 373) ^ 186 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 373) ^ 186 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 373) ^ 124 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 373) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_379 : Nat.Prime 379 := by
  apply lucas_from_prime_list 379 (2 : ZMod 379) [2,3,3,3,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 379) ^ 378 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 379) ^ 189 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 379) ^ 126 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 379) ^ 126 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 379) ^ 126 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 379) ^ 54 ≠ 1
      reduce_mod_char
      decide

private lemma prime_383 : Nat.Prime 383 := by
  apply lucas_from_prime_list 383 (5 : ZMod 383) [2,191]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_191
  · decide +kernel
  · change (5 : ZMod 383) ^ 382 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 383) ^ 191 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 383) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_389 : Nat.Prime 389 := by
  apply lucas_from_prime_list 389 (2 : ZMod 389) [2,2,97]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_97
  · decide +kernel
  · change (2 : ZMod 389) ^ 388 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 389) ^ 194 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 389) ^ 194 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 389) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_397 : Nat.Prime 397 := by
  apply lucas_from_prime_list 397 (5 : ZMod 397) [2,2,3,3,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_11
  · decide +kernel
  · change (5 : ZMod 397) ^ 396 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 397) ^ 198 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 397) ^ 198 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 397) ^ 132 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 397) ^ 132 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 397) ^ 36 ≠ 1
      reduce_mod_char
      decide

private lemma prime_409 : Nat.Prime 409 := by
  apply lucas_from_prime_list 409 (21 : ZMod 409) [2,2,2,3,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel
  · change (21 : ZMod 409) ^ 408 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 409) ^ 204 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 409) ^ 204 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 409) ^ 204 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 409) ^ 136 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 409) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_419 : Nat.Prime 419 := by
  apply lucas_from_prime_list 419 (2 : ZMod 419) [2,11,19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
  · decide +kernel
  · change (2 : ZMod 419) ^ 418 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 419) ^ 209 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 419) ^ 38 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 419) ^ 22 ≠ 1
      reduce_mod_char
      decide

private lemma prime_421 : Nat.Prime 421 := by
  apply lucas_from_prime_list 421 (2 : ZMod 421) [2,2,3,5,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 421) ^ 420 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 421) ^ 210 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 421) ^ 210 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 421) ^ 140 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 421) ^ 84 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 421) ^ 60 ≠ 1
      reduce_mod_char
      decide

private lemma prime_431 : Nat.Prime 431 := by
  apply lucas_from_prime_list 431 (7 : ZMod 431) [2,5,43]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
  · decide +kernel
  · change (7 : ZMod 431) ^ 430 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 431) ^ 215 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 431) ^ 86 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 431) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_433 : Nat.Prime 433 := by
  apply lucas_from_prime_list 433 (5 : ZMod 433) [2,2,2,2,3,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (5 : ZMod 433) ^ 432 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 433) ^ 216 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 433) ^ 216 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 433) ^ 216 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 433) ^ 216 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 433) ^ 144 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 433) ^ 144 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 433) ^ 144 ≠ 1
      reduce_mod_char
      decide

private lemma prime_439 : Nat.Prime 439 := by
  apply lucas_from_prime_list 439 (15 : ZMod 439) [2,3,73]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
  · decide +kernel
  · change (15 : ZMod 439) ^ 438 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (15 : ZMod 439) ^ 219 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 439) ^ 146 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 439) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_443 : Nat.Prime 443 := by
  apply lucas_from_prime_list 443 (2 : ZMod 443) [2,13,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
  · decide +kernel
  · change (2 : ZMod 443) ^ 442 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 443) ^ 221 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 443) ^ 34 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 443) ^ 26 ≠ 1
      reduce_mod_char
      decide

private lemma prime_449 : Nat.Prime 449 := by
  apply lucas_from_prime_list 449 (3 : ZMod 449) [2,2,2,2,2,2,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
  · decide +kernel
  · change (3 : ZMod 449) ^ 448 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 64 ≠ 1
      reduce_mod_char
      decide

private lemma prime_457 : Nat.Prime 457 := by
  apply lucas_from_prime_list 457 (13 : ZMod 457) [2,2,2,3,19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel
  · change (13 : ZMod 457) ^ 456 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 457) ^ 228 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 457) ^ 228 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 457) ^ 228 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 457) ^ 152 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 457) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_461 : Nat.Prime 461 := by
  apply lucas_from_prime_list 461 (2 : ZMod 461) [2,2,5,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_23
  · decide +kernel
  · change (2 : ZMod 461) ^ 460 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 461) ^ 230 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 461) ^ 230 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 461) ^ 92 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 461) ^ 20 ≠ 1
      reduce_mod_char
      decide

private lemma prime_463 : Nat.Prime 463 := by
  apply lucas_from_prime_list 463 (3 : ZMod 463) [2,3,7,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel
  · change (3 : ZMod 463) ^ 462 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 463) ^ 231 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 463) ^ 154 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 463) ^ 66 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 463) ^ 42 ≠ 1
      reduce_mod_char
      decide

private lemma prime_467 : Nat.Prime 467 := by
  apply lucas_from_prime_list 467 (2 : ZMod 467) [2,233]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_233
  · decide +kernel
  · change (2 : ZMod 467) ^ 466 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 467) ^ 233 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 467) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_487 : Nat.Prime 487 := by
  apply lucas_from_prime_list 487 (3 : ZMod 487) [2,3,3,3,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (3 : ZMod 487) ^ 486 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 487) ^ 243 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 487) ^ 162 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 487) ^ 162 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 487) ^ 162 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 487) ^ 162 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 487) ^ 162 ≠ 1
      reduce_mod_char
      decide

private lemma prime_509 : Nat.Prime 509 := by
  apply lucas_from_prime_list 509 (2 : ZMod 509) [2,2,127]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_127
  · decide +kernel
  · change (2 : ZMod 509) ^ 508 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 509) ^ 254 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 509) ^ 254 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 509) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_521 : Nat.Prime 521 := by
  apply lucas_from_prime_list 521 (3 : ZMod 521) [2,2,2,5,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel
  · change (3 : ZMod 521) ^ 520 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 521) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 521) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 521) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 521) ^ 104 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 521) ^ 40 ≠ 1
      reduce_mod_char
      decide

private lemma prime_523 : Nat.Prime 523 := by
  apply lucas_from_prime_list 523 (2 : ZMod 523) [2,3,3,29]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_29
  · decide +kernel
  · change (2 : ZMod 523) ^ 522 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 523) ^ 261 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 523) ^ 174 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 523) ^ 174 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 523) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_557 : Nat.Prime 557 := by
  apply lucas_from_prime_list 557 (2 : ZMod 557) [2,2,139]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_139
  · decide +kernel
  · change (2 : ZMod 557) ^ 556 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 557) ^ 278 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 557) ^ 278 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 557) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_577 : Nat.Prime 577 := by
  apply lucas_from_prime_list 577 (5 : ZMod 577) [2,2,2,2,2,2,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (5 : ZMod 577) ^ 576 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 577) ^ 288 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 577) ^ 288 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 577) ^ 288 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 577) ^ 288 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 577) ^ 288 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 577) ^ 288 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 577) ^ 192 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 577) ^ 192 ≠ 1
      reduce_mod_char
      decide

private lemma prime_607 : Nat.Prime 607 := by
  apply lucas_from_prime_list 607 (3 : ZMod 607) [2,3,101]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
  · decide +kernel
  · change (3 : ZMod 607) ^ 606 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 607) ^ 303 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 607) ^ 202 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 607) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_617 : Nat.Prime 617 := by
  apply lucas_from_prime_list 617 (3 : ZMod 617) [2,2,2,7,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_11
  · decide +kernel
  · change (3 : ZMod 617) ^ 616 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 617) ^ 308 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 617) ^ 308 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 617) ^ 308 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 617) ^ 88 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 617) ^ 56 ≠ 1
      reduce_mod_char
      decide

private lemma prime_641 : Nat.Prime 641 := by
  apply lucas_from_prime_list 641 (3 : ZMod 641) [2,2,2,2,2,2,2,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
  · decide +kernel
  · change (3 : ZMod 641) ^ 640 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 641) ^ 320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 641) ^ 320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 641) ^ 320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 641) ^ 320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 641) ^ 320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 641) ^ 320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 641) ^ 320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 641) ^ 128 ≠ 1
      reduce_mod_char
      decide

private lemma prime_643 : Nat.Prime 643 := by
  apply lucas_from_prime_list 643 (11 : ZMod 643) [2,3,107]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
  · decide +kernel
  · change (11 : ZMod 643) ^ 642 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (11 : ZMod 643) ^ 321 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 643) ^ 214 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 643) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_733 : Nat.Prime 733 := by
  apply lucas_from_prime_list 733 (6 : ZMod 733) [2,2,3,61]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_61
  · decide +kernel
  · change (6 : ZMod 733) ^ 732 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 733) ^ 366 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 733) ^ 366 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 733) ^ 244 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 733) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_751 : Nat.Prime 751 := by
  apply lucas_from_prime_list 751 (3 : ZMod 751) [2,3,5,5,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5
    · exact prime_5
  · decide +kernel
  · change (3 : ZMod 751) ^ 750 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 751) ^ 375 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 751) ^ 250 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 751) ^ 150 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 751) ^ 150 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 751) ^ 150 ≠ 1
      reduce_mod_char
      decide

private lemma prime_853 : Nat.Prime 853 := by
  apply lucas_from_prime_list 853 (2 : ZMod 853) [2,2,3,71]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_71
  · decide +kernel
  · change (2 : ZMod 853) ^ 852 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 853) ^ 426 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 853) ^ 426 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 853) ^ 284 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 853) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_919 : Nat.Prime 919 := by
  apply lucas_from_prime_list 919 (7 : ZMod 919) [2,3,3,3,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_17
  · decide +kernel
  · change (7 : ZMod 919) ^ 918 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 919) ^ 459 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 919) ^ 306 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 919) ^ 306 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 919) ^ 306 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 919) ^ 54 ≠ 1
      reduce_mod_char
      decide

private lemma prime_997 : Nat.Prime 997 := by
  apply lucas_from_prime_list 997 (7 : ZMod 997) [2,2,3,83]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel
  · change (7 : ZMod 997) ^ 996 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (7 : ZMod 997) ^ 498 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 997) ^ 498 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 997) ^ 332 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 997) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1087 : Nat.Prime 1087 := by
  apply lucas_from_prime_list 1087 (3 : ZMod 1087) [2,3,181]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
  · decide +kernel
  · change (3 : ZMod 1087) ^ 1086 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 1087) ^ 543 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1087) ^ 362 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1087) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1129 : Nat.Prime 1129 := by
  apply lucas_from_prime_list 1129 (11 : ZMod 1129) [2,2,2,3,47]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel
  · change (11 : ZMod 1129) ^ 1128 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1129) ^ 564 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 1129) ^ 564 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 1129) ^ 564 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 1129) ^ 376 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 1129) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_11027 : Nat.Prime 11027 := by
  apply lucas_from_prime_list 11027 (2 : ZMod 11027) [2,37,149]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_149
  · decide +kernel
  · change (2 : ZMod 11027) ^ 11026 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 11027) ^ 5513 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 11027) ^ 298 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 11027) ^ 74 ≠ 1
      reduce_mod_char
      decide

private lemma prime_144100836001 : Nat.Prime 144100836001 := by
  apply lucas_from_prime_list 144100836001 (14 : ZMod 144100836001) [2,2,2,2,2,3,3,3,5,5,5,11,11,11027]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_5
    · exact prime_5
    · exact prime_11
    · exact prime_11
    · exact prime_11027
  · decide +kernel
  · change (14 : ZMod 144100836001) ^ 144100836000 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 144100836001) ^ 72050418000 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 72050418000 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 72050418000 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 72050418000 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 72050418000 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 48033612000 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 48033612000 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 48033612000 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 28820167200 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 28820167200 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 28820167200 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 13100076000 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 13100076000 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 144100836001) ^ 13068000 ≠ 1
      reduce_mod_char
      decide

private lemma prime_154213 : Nat.Prime 154213 := by
  apply lucas_from_prime_list 154213 (2 : ZMod 154213) [2,2,3,71,181]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_181
  · decide +kernel
  · change (2 : ZMod 154213) ^ 154212 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 154213) ^ 77106 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 154213) ^ 77106 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 154213) ^ 51404 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 154213) ^ 2172 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 154213) ^ 852 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999998341 : Nat.Prime 3999999999999998341 := by
  apply lucas_from_prime_list 3999999999999998341 (2 : ZMod 3999999999999998341) [2,2,3,3,5,154213,144100836001]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_154213
    · exact prime_144100836001
  · decide +kernel
  · change (2 : ZMod 3999999999999998341) ^ 3999999999999998340 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3999999999999998341) ^ 1999999999999999170 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998341) ^ 1999999999999999170 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998341) ^ 1333333333333332780 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998341) ^ 1333333333333332780 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998341) ^ 799999999999999668 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998341) ^ 25938150480180 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998341) ^ 27758340 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1193 : Nat.Prime 1193 := by
  apply lucas_from_prime_list 1193 (3 : ZMod 1193) [2,2,2,149]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_149
  · decide +kernel
  · change (3 : ZMod 1193) ^ 1192 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1193) ^ 596 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1193) ^ 596 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1193) ^ 596 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1193) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_8017 : Nat.Prime 8017 := by
  apply lucas_from_prime_list 8017 (5 : ZMod 8017) [2,2,2,2,3,167]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_167
  · decide +kernel
  · change (5 : ZMod 8017) ^ 8016 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8017) ^ 4008 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 8017) ^ 4008 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 8017) ^ 4008 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 8017) ^ 4008 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 8017) ^ 2672 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 8017) ^ 48 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3495413 : Nat.Prime 3495413 := by
  apply lucas_from_prime_list 3495413 (2 : ZMod 3495413) [2,2,109,8017]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_109
    · exact prime_8017
  · decide +kernel
  · change (2 : ZMod 3495413) ^ 3495412 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3495413) ^ 1747706 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3495413) ^ 1747706 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3495413) ^ 32068 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3495413) ^ 436 ≠ 1
      reduce_mod_char
      decide

private lemma prime_479 : Nat.Prime 479 := by
  apply lucas_from_prime_list 479 (13 : ZMod 479) [2,239]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_239
  · decide +kernel
  · change (13 : ZMod 479) ^ 478 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (13 : ZMod 479) ^ 239 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 479) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_34925956971221 : Nat.Prime 34925956971221 := by
  apply lucas_from_prime_list 34925956971221 (2 : ZMod 34925956971221) [2,2,5,7,149,479,3495413]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_149
    · exact prime_479
    · exact prime_3495413
  · decide +kernel
  · change (2 : ZMod 34925956971221) ^ 34925956971220 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34925956971221) ^ 17462978485610 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 34925956971221) ^ 17462978485610 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 34925956971221) ^ 6985191394244 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 34925956971221) ^ 4989422424460 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 34925956971221) ^ 234402395780 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 34925956971221) ^ 72914315180 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 34925956971221) ^ 9991940 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999998689 : Nat.Prime 3999999999999998689 := by
  apply lucas_from_prime_list 3999999999999998689 (11 : ZMod 3999999999999998689) [2,2,2,2,2,3,1193,34925956971221]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_1193
    · exact prime_34925956971221
  · decide +kernel
  · change (11 : ZMod 3999999999999998689) ^ 3999999999999998688 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3999999999999998689) ^ 1999999999999999344 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3999999999999998689) ^ 1999999999999999344 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3999999999999998689) ^ 1999999999999999344 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3999999999999998689) ^ 1999999999999999344 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3999999999999998689) ^ 1999999999999999344 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3999999999999998689) ^ 1333333333333332896 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3999999999999998689) ^ 3352891869237216 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3999999999999998689) ^ 114528 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3527 : Nat.Prime 3527 := by
  apply lucas_from_prime_list 3527 (5 : ZMod 3527) [2,41,43]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_43
  · decide +kernel
  · change (5 : ZMod 3527) ^ 3526 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 3527) ^ 1763 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3527) ^ 86 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3527) ^ 82 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1128641 : Nat.Prime 1128641 := by
  apply lucas_from_prime_list 1128641 (3 : ZMod 1128641) [2,2,2,2,2,2,5,3527]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_3527
  · decide +kernel
  · change (3 : ZMod 1128641) ^ 1128640 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1128641) ^ 564320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1128641) ^ 564320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1128641) ^ 564320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1128641) ^ 564320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1128641) ^ 564320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1128641) ^ 564320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1128641) ^ 225728 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1128641) ^ 320 ≠ 1
      reduce_mod_char
      decide

private lemma prime_135409 : Nat.Prime 135409 := by
  apply lucas_from_prime_list 135409 (11 : ZMod 135409) [2,2,2,2,3,7,13,31]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_31
  · decide +kernel
  · change (11 : ZMod 135409) ^ 135408 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 135409) ^ 67704 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 135409) ^ 67704 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 135409) ^ 67704 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 135409) ^ 67704 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 135409) ^ 45136 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 135409) ^ 19344 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 135409) ^ 10416 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 135409) ^ 4368 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2978999 : Nat.Prime 2978999 := by
  apply lucas_from_prime_list 2978999 (7 : ZMod 2978999) [2,11,135409]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_135409
  · decide +kernel
  · change (7 : ZMod 2978999) ^ 2978998 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 2978999) ^ 1489499 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 2978999) ^ 270818 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 2978999) ^ 22 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999998711 : Nat.Prime 3999999999999998711 := by
  apply lucas_from_prime_list 3999999999999998711 (19 : ZMod 3999999999999998711) [2,5,271,439,1128641,2978999]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_271
    · exact prime_439
    · exact prime_1128641
    · exact prime_2978999
  · decide +kernel
  · change (19 : ZMod 3999999999999998711) ^ 3999999999999998710 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 3999999999999998711) ^ 1999999999999999355 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999998711) ^ 799999999999999742 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999998711) ^ 14760147601476010 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999998711) ^ 9111617312072890 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999998711) ^ 3544085320310 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999998711) ^ 1342732911290 ≠ 1
      reduce_mod_char
      decide

private lemma prime_13331 : Nat.Prime 13331 := by
  apply lucas_from_prime_list 13331 (2 : ZMod 13331) [2,5,31,43]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_43
  · decide +kernel
  · change (2 : ZMod 13331) ^ 13330 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13331) ^ 6665 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 13331) ^ 2666 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 13331) ^ 430 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 13331) ^ 310 ≠ 1
      reduce_mod_char
      decide

private lemma prime_811 : Nat.Prime 811 := by
  apply lucas_from_prime_list 811 (3 : ZMod 811) [2,3,3,3,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (3 : ZMod 811) ^ 810 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 811) ^ 405 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 811) ^ 270 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 811) ^ 270 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 811) ^ 270 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 811) ^ 270 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 811) ^ 162 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1481 : Nat.Prime 1481 := by
  apply lucas_from_prime_list 1481 (3 : ZMod 1481) [2,2,2,5,37]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_37
  · decide +kernel
  · change (3 : ZMod 1481) ^ 1480 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1481) ^ 740 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1481) ^ 740 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1481) ^ 740 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1481) ^ 296 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1481) ^ 40 ≠ 1
      reduce_mod_char
      decide

private lemma prime_8887 : Nat.Prime 8887 := by
  apply lucas_from_prime_list 8887 (3 : ZMod 8887) [2,3,1481]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1481
  · decide +kernel
  · change (3 : ZMod 8887) ^ 8886 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 8887) ^ 4443 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 8887) ^ 2962 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 8887) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3359287 : Nat.Prime 3359287 := by
  apply lucas_from_prime_list 3359287 (5 : ZMod 3359287) [2,3,3,3,7,8887]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_7
    · exact prime_8887
  · decide +kernel
  · change (5 : ZMod 3359287) ^ 3359286 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3359287) ^ 1679643 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3359287) ^ 1119762 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3359287) ^ 1119762 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3359287) ^ 1119762 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3359287) ^ 479898 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3359287) ^ 378 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1923413520443 : Nat.Prime 1923413520443 := by
  apply lucas_from_prime_list 1923413520443 (2 : ZMod 1923413520443) [2,353,811,3359287]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_811
    · exact prime_3359287
  · decide +kernel
  · change (2 : ZMod 1923413520443) ^ 1923413520442 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1923413520443) ^ 961706760221 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1923413520443) ^ 5448763514 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1923413520443) ^ 2371656622 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1923413520443) ^ 572566 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999998749 : Nat.Prime 3999999999999998749 := by
  apply lucas_from_prime_list 3999999999999998749 (7 : ZMod 3999999999999998749) [2,2,3,13,13331,1923413520443]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_13331
    · exact prime_1923413520443
  · decide +kernel
  · change (7 : ZMod 3999999999999998749) ^ 3999999999999998748 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3999999999999998749) ^ 1999999999999999374 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999998749) ^ 1999999999999999374 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999998749) ^ 1333333333333332916 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999998749) ^ 307692307692307596 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999998749) ^ 300052509189108 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999998749) ^ 2079636 ≠ 1
      reduce_mod_char
      decide

private lemma prime_158475857 : Nat.Prime 158475857 := by
  apply lucas_from_prime_list 158475857 (3 : ZMod 158475857) [2,2,2,2,7,11,307,419]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_307
    · exact prime_419
  · decide +kernel
  · change (3 : ZMod 158475857) ^ 158475856 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 158475857) ^ 79237928 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158475857) ^ 79237928 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158475857) ^ 79237928 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158475857) ^ 79237928 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158475857) ^ 22639408 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158475857) ^ 14406896 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158475857) ^ 516208 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158475857) ^ 378224 ≠ 1
      reduce_mod_char
      decide

private lemma prime_311 : Nat.Prime 311 := by
  apply lucas_from_prime_list 311 (17 : ZMod 311) [2,5,31]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
  · decide +kernel
  · change (17 : ZMod 311) ^ 310 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (17 : ZMod 311) ^ 155 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 311) ^ 62 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 311) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_17417 : Nat.Prime 17417 := by
  apply lucas_from_prime_list 17417 (3 : ZMod 17417) [2,2,2,7,311]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_311
  · decide +kernel
  · change (3 : ZMod 17417) ^ 17416 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17417) ^ 8708 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 17417) ^ 8708 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 17417) ^ 8708 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 17417) ^ 2488 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 17417) ^ 56 ≠ 1
      reduce_mod_char
      decide

private lemma prime_60723828030119 : Nat.Prime 60723828030119 := by
  apply lucas_from_prime_list 60723828030119 (11 : ZMod 60723828030119) [2,11,17417,158475857]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17417
    · exact prime_158475857
  · decide +kernel
  · change (11 : ZMod 60723828030119) ^ 60723828030118 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (11 : ZMod 60723828030119) ^ 30361914015059 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 60723828030119) ^ 5520348002738 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 60723828030119) ^ 3486468854 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 60723828030119) ^ 383174 ≠ 1
      reduce_mod_char
      decide

private lemma prime_499999999999999847 : Nat.Prime 499999999999999847 := by
  apply lucas_from_prime_list 499999999999999847 (5 : ZMod 499999999999999847) [2,23,179,60723828030119]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_179
    · exact prime_60723828030119
  · decide +kernel
  · change (5 : ZMod 499999999999999847) ^ 499999999999999846 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 499999999999999847) ^ 249999999999999923 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 499999999999999847) ^ 21739130434782602 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 499999999999999847) ^ 2793296089385474 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 499999999999999847) ^ 8234 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999998777 : Nat.Prime 3999999999999998777 := by
  apply lucas_from_prime_list 3999999999999998777 (3 : ZMod 3999999999999998777) [2,2,2,499999999999999847]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_499999999999999847
  · decide +kernel
  · change (3 : ZMod 3999999999999998777) ^ 3999999999999998776 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3999999999999998777) ^ 1999999999999999388 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999998777) ^ 1999999999999999388 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999998777) ^ 1999999999999999388 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999998777) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_8429 : Nat.Prime 8429 := by
  apply lucas_from_prime_list 8429 (2 : ZMod 8429) [2,2,7,7,43]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_7
    · exact prime_43
  · decide +kernel
  · change (2 : ZMod 8429) ^ 8428 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8429) ^ 4214 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 8429) ^ 4214 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 8429) ^ 1204 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 8429) ^ 1204 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 8429) ^ 196 ≠ 1
      reduce_mod_char
      decide

private lemma prime_40763 : Nat.Prime 40763 := by
  apply lucas_from_prime_list 40763 (2 : ZMod 40763) [2,89,229]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_229
  · decide +kernel
  · change (2 : ZMod 40763) ^ 40762 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 40763) ^ 20381 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 40763) ^ 458 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 40763) ^ 178 ≠ 1
      reduce_mod_char
      decide

private lemma prime_42393521 : Nat.Prime 42393521 := by
  apply lucas_from_prime_list 42393521 (3 : ZMod 42393521) [2,2,2,2,5,13,40763]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_40763
  · decide +kernel
  · change (3 : ZMod 42393521) ^ 42393520 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42393521) ^ 21196760 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 42393521) ^ 21196760 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 42393521) ^ 21196760 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 42393521) ^ 21196760 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 42393521) ^ 8478704 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 42393521) ^ 3261040 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 42393521) ^ 1040 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4073 : Nat.Prime 4073 := by
  apply lucas_from_prime_list 4073 (3 : ZMod 4073) [2,2,2,509]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_509
  · decide +kernel
  · change (3 : ZMod 4073) ^ 4072 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4073) ^ 2036 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4073) ^ 2036 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4073) ^ 2036 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4073) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_8147 : Nat.Prime 8147 := by
  apply lucas_from_prime_list 8147 (2 : ZMod 8147) [2,4073]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_4073
  · decide +kernel
  · change (2 : ZMod 8147) ^ 8146 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 8147) ^ 4073 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 8147) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999998803 : Nat.Prime 3999999999999998803 := by
  apply lucas_from_prime_list 3999999999999998803 (2 : ZMod 3999999999999998803) [2,3,229,8147,8429,42393521]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
    · exact prime_8147
    · exact prime_8429
    · exact prime_42393521
  · decide +kernel
  · change (2 : ZMod 3999999999999998803) ^ 3999999999999998802 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3999999999999998803) ^ 1999999999999999401 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998803) ^ 1333333333333332934 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998803) ^ 17467248908296938 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998803) ^ 490978274211366 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998803) ^ 474552141416538 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998803) ^ 94354040562 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2748826133 : Nat.Prime 2748826133 := by
  apply lucas_from_prime_list 2748826133 (3 : ZMod 2748826133) [2,2,13,29,53,163,211]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_53
    · exact prime_163
    · exact prime_211
  · decide +kernel
  · change (3 : ZMod 2748826133) ^ 2748826132 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2748826133) ^ 1374413066 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2748826133) ^ 1374413066 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2748826133) ^ 211448164 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2748826133) ^ 94787108 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2748826133) ^ 51864644 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2748826133) ^ 16863964 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2748826133) ^ 13027612 ≠ 1
      reduce_mod_char
      decide

private lemma prime_65971827193 : Nat.Prime 65971827193 := by
  apply lucas_from_prime_list 65971827193 (5 : ZMod 65971827193) [2,2,2,3,2748826133]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_2748826133
  · decide +kernel
  · change (5 : ZMod 65971827193) ^ 65971827192 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 65971827193) ^ 32985913596 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 65971827193) ^ 32985913596 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 65971827193) ^ 32985913596 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 65971827193) ^ 21990609064 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 65971827193) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_63689 : Nat.Prime 63689 := by
  apply lucas_from_prime_list 63689 (3 : ZMod 63689) [2,2,2,19,419]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_19
    · exact prime_419
  · decide +kernel
  · change (3 : ZMod 63689) ^ 63688 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63689) ^ 31844 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 63689) ^ 31844 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 63689) ^ 31844 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 63689) ^ 3352 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 63689) ^ 152 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4330853 : Nat.Prime 4330853 := by
  apply lucas_from_prime_list 4330853 (2 : ZMod 4330853) [2,2,17,63689]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_17
    · exact prime_63689
  · decide +kernel
  · change (2 : ZMod 4330853) ^ 4330852 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4330853) ^ 2165426 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4330853) ^ 2165426 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4330853) ^ 254756 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4330853) ^ 68 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999998807 : Nat.Prime 3999999999999998807 := by
  apply lucas_from_prime_list 3999999999999998807 (5 : ZMod 3999999999999998807) [2,7,4330853,65971827193]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4330853
    · exact prime_65971827193
  · decide +kernel
  · change (5 : ZMod 3999999999999998807) ^ 3999999999999998806 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3999999999999998807) ^ 1999999999999999403 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999998807) ^ 571428571428571258 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999998807) ^ 923605580702 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999998807) ^ 60631942 ≠ 1
      reduce_mod_char
      decide

private lemma prime_158974471 : Nat.Prime 158974471 := by
  apply lucas_from_prime_list 158974471 (3 : ZMod 158974471) [2,3,3,5,89,89,223]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_89
    · exact prime_223
  · decide +kernel
  · change (3 : ZMod 158974471) ^ 158974470 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 158974471) ^ 79487235 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158974471) ^ 52991490 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158974471) ^ 52991490 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158974471) ^ 31794894 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158974471) ^ 1786230 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158974471) ^ 1786230 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 158974471) ^ 712890 ≠ 1
      reduce_mod_char
      decide

private lemma prime_10333 : Nat.Prime 10333 := by
  apply lucas_from_prime_list 10333 (5 : ZMod 10333) [2,2,3,3,7,41]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_7
    · exact prime_41
  · decide +kernel
  · change (5 : ZMod 10333) ^ 10332 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10333) ^ 5166 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 10333) ^ 5166 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 10333) ^ 3444 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 10333) ^ 3444 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 10333) ^ 1476 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 10333) ^ 252 ≠ 1
      reduce_mod_char
      decide

private lemma prime_5889811 : Nat.Prime 5889811 := by
  apply lucas_from_prime_list 5889811 (2 : ZMod 5889811) [2,3,5,19,10333]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_10333
  · decide +kernel
  · change (2 : ZMod 5889811) ^ 5889810 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5889811) ^ 2944905 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 5889811) ^ 1963270 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 5889811) ^ 1177962 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 5889811) ^ 309990 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 5889811) ^ 570 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999998833 : Nat.Prime 3999999999999998833 := by
  apply lucas_from_prime_list 3999999999999998833 (5 : ZMod 3999999999999998833) [2,2,2,2,3,89,5889811,158974471]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_5889811
    · exact prime_158974471
  · decide +kernel
  · change (5 : ZMod 3999999999999998833) ^ 3999999999999998832 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3999999999999998833) ^ 1999999999999999416 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999998833) ^ 1999999999999999416 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999998833) ^ 1999999999999999416 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999998833) ^ 1999999999999999416 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999998833) ^ 1333333333333332944 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999998833) ^ 44943820224719088 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999998833) ^ 679138940112 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999998833) ^ 25161272592 ≠ 1
      reduce_mod_char
      decide

private lemma prime_17026637 : Nat.Prime 17026637 := by
  apply lucas_from_prime_list 17026637 (2 : ZMod 17026637) [2,2,11,11,127,277]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_11
    · exact prime_11
    · exact prime_127
    · exact prime_277
  · decide +kernel
  · change (2 : ZMod 17026637) ^ 17026636 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17026637) ^ 8513318 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 17026637) ^ 8513318 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 17026637) ^ 1547876 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 17026637) ^ 1547876 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 17026637) ^ 134068 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 17026637) ^ 61468 ≠ 1
      reduce_mod_char
      decide

private lemma prime_16069 : Nat.Prime 16069 := by
  apply lucas_from_prime_list 16069 (2 : ZMod 16069) [2,2,3,13,103]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_103
  · decide +kernel
  · change (2 : ZMod 16069) ^ 16068 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16069) ^ 8034 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 16069) ^ 8034 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 16069) ^ 5356 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 16069) ^ 1236 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 16069) ^ 156 ≠ 1
      reduce_mod_char
      decide

private lemma prime_977 : Nat.Prime 977 := by
  apply lucas_from_prime_list 977 (3 : ZMod 977) [2,2,2,2,61]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_61
  · decide +kernel
  · change (3 : ZMod 977) ^ 976 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 977) ^ 488 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 977) ^ 488 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 977) ^ 488 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 977) ^ 488 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 977) ^ 16 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2731697863 : Nat.Prime 2731697863 := by
  apply lucas_from_prime_list 2731697863 (3 : ZMod 2731697863) [2,3,29,977,16069]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_977
    · exact prime_16069
  · decide +kernel
  · change (3 : ZMod 2731697863) ^ 2731697862 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2731697863) ^ 1365848931 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2731697863) ^ 910565954 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2731697863) ^ 94196478 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2731697863) ^ 2796006 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2731697863) ^ 169998 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999998867 : Nat.Prime 3999999999999998867 := by
  apply lucas_from_prime_list 3999999999999998867 (2 : ZMod 3999999999999998867) [2,43,17026637,2731697863]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_17026637
    · exact prime_2731697863
  · decide +kernel
  · change (2 : ZMod 3999999999999998867) ^ 3999999999999998866 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3999999999999998867) ^ 1999999999999999433 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998867) ^ 93023255813953462 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998867) ^ 234926016218 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998867) ^ 1464290782 ≠ 1
      reduce_mod_char
      decide

private lemma prime_691 : Nat.Prime 691 := by
  apply lucas_from_prime_list 691 (3 : ZMod 691) [2,3,5,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel
  · change (3 : ZMod 691) ^ 690 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 691) ^ 345 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 691) ^ 230 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 691) ^ 138 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 691) ^ 30 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2111 : Nat.Prime 2111 := by
  apply lucas_from_prime_list 2111 (7 : ZMod 2111) [2,5,211]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_211
  · decide +kernel
  · change (7 : ZMod 2111) ^ 2110 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 2111) ^ 1055 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 2111) ^ 422 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 2111) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2917403 : Nat.Prime 2917403 := by
  apply lucas_from_prime_list 2917403 (2 : ZMod 2917403) [2,691,2111]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_691
    · exact prime_2111
  · decide +kernel
  · change (2 : ZMod 2917403) ^ 2917402 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 2917403) ^ 1458701 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2917403) ^ 4222 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2917403) ^ 1382 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1669 : Nat.Prime 1669 := by
  apply lucas_from_prime_list 1669 (2 : ZMod 1669) [2,2,3,139]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_139
  · decide +kernel
  · change (2 : ZMod 1669) ^ 1668 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1669) ^ 834 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1669) ^ 834 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1669) ^ 556 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1669) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_38953164857 : Nat.Prime 38953164857 := by
  apply lucas_from_prime_list 38953164857 (3 : ZMod 38953164857) [2,2,2,1669,2917403]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_1669
    · exact prime_2917403
  · decide +kernel
  · change (3 : ZMod 38953164857) ^ 38953164856 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38953164857) ^ 19476582428 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 38953164857) ^ 19476582428 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 38953164857) ^ 19476582428 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 38953164857) ^ 23339224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 38953164857) ^ 13352 ≠ 1
      reduce_mod_char
      decide

private lemma prime_991 : Nat.Prime 991 := by
  apply lucas_from_prime_list 991 (6 : ZMod 991) [2,3,3,5,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel
  · change (6 : ZMod 991) ^ 990 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 991) ^ 495 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 991) ^ 330 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 991) ^ 330 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 991) ^ 198 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 991) ^ 90 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999998941 : Nat.Prime 3999999999999998941 := by
  apply lucas_from_prime_list 3999999999999998941 (2 : ZMod 3999999999999998941) [2,2,3,5,11,157,991,38953164857]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_157
    · exact prime_991
    · exact prime_38953164857
  · decide +kernel
  · change (2 : ZMod 3999999999999998941) ^ 3999999999999998940 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3999999999999998941) ^ 1999999999999999470 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998941) ^ 1999999999999999470 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998941) ^ 1333333333333332980 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998941) ^ 799999999999999788 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998941) ^ 363636363636363540 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998941) ^ 25477707006369420 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998941) ^ 4036326942482340 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999998941) ^ 102687420 ≠ 1
      reduce_mod_char
      decide

private lemma prime_392827 : Nat.Prime 392827 := by
  apply lucas_from_prime_list 392827 (2 : ZMod 392827) [2,3,7,47,199]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_199
  · decide +kernel
  · change (2 : ZMod 392827) ^ 392826 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 392827) ^ 196413 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 392827) ^ 130942 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 392827) ^ 56118 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 392827) ^ 8358 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 392827) ^ 1974 ≠ 1
      reduce_mod_char
      decide

private lemma prime_5239526527 : Nat.Prime 5239526527 := by
  apply lucas_from_prime_list 5239526527 (3 : ZMod 5239526527) [2,3,3,3,13,19,392827]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_392827
  · decide +kernel
  · change (3 : ZMod 5239526527) ^ 5239526526 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5239526527) ^ 2619763263 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5239526527) ^ 1746508842 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5239526527) ^ 1746508842 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5239526527) ^ 1746508842 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5239526527) ^ 403040502 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5239526527) ^ 275764554 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5239526527) ^ 13338 ≠ 1
      reduce_mod_char
      decide

private lemma prime_125748636649 : Nat.Prime 125748636649 := by
  apply lucas_from_prime_list 125748636649 (17 : ZMod 125748636649) [2,2,2,3,5239526527]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5239526527
  · decide +kernel
  · change (17 : ZMod 125748636649) ^ 125748636648 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 125748636649) ^ 62874318324 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 125748636649) ^ 62874318324 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 125748636649) ^ 62874318324 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 125748636649) ^ 41916212216 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 125748636649) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999011 : Nat.Prime 3999999999999999011 := by
  apply lucas_from_prime_list 3999999999999999011 (2 : ZMod 3999999999999999011) [2,5,89,103,347,125748636649]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_103
    · exact prime_347
    · exact prime_125748636649
  · decide +kernel
  · change (2 : ZMod 3999999999999999011) ^ 3999999999999999010 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3999999999999999011) ^ 1999999999999999505 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999011) ^ 799999999999999802 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999011) ^ 44943820224719090 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999011) ^ 38834951456310670 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999011) ^ 11527377521613830 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999011) ^ 31809490 ≠ 1
      reduce_mod_char
      decide

private lemma prime_6287 : Nat.Prime 6287 := by
  apply lucas_from_prime_list 6287 (7 : ZMod 6287) [2,7,449]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_449
  · decide +kernel
  · change (7 : ZMod 6287) ^ 6286 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 6287) ^ 3143 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 6287) ^ 898 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 6287) ^ 14 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2926699093 : Nat.Prime 2926699093 := by
  apply lucas_from_prime_list 2926699093 (2 : ZMod 2926699093) [2,2,3,3,67,193,6287]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_67
    · exact prime_193
    · exact prime_6287
  · decide +kernel
  · change (2 : ZMod 2926699093) ^ 2926699092 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2926699093) ^ 1463349546 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2926699093) ^ 1463349546 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2926699093) ^ 975566364 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2926699093) ^ 975566364 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2926699093) ^ 43682076 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2926699093) ^ 15164244 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2926699093) ^ 465516 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4391 : Nat.Prime 4391 := by
  apply lucas_from_prime_list 4391 (14 : ZMod 4391) [2,5,439]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_439
  · decide +kernel
  · change (14 : ZMod 4391) ^ 4390 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (14 : ZMod 4391) ^ 2195 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 4391) ^ 878 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 4391) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_579613 : Nat.Prime 579613 := by
  apply lucas_from_prime_list 579613 (2 : ZMod 579613) [2,2,3,11,4391]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4391
  · decide +kernel
  · change (2 : ZMod 579613) ^ 579612 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 579613) ^ 289806 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 579613) ^ 289806 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 579613) ^ 193204 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 579613) ^ 52692 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 579613) ^ 132 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999223 : Nat.Prime 3999999999999999223 := by
  apply lucas_from_prime_list 3999999999999999223 (3 : ZMod 3999999999999999223) [2,3,3,131,579613,2926699093]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_131
    · exact prime_579613
    · exact prime_2926699093
  · decide +kernel
  · change (3 : ZMod 3999999999999999223) ^ 3999999999999999222 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3999999999999999223) ^ 1999999999999999611 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999223) ^ 1333333333333333074 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999223) ^ 1333333333333333074 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999223) ^ 30534351145038162 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999223) ^ 6901156461294 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999223) ^ 1366727454 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1667 : Nat.Prime 1667 := by
  apply lucas_from_prime_list 1667 (2 : ZMod 1667) [2,7,7,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7
    · exact prime_17
  · decide +kernel
  · change (2 : ZMod 1667) ^ 1666 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1667) ^ 833 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1667) ^ 238 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1667) ^ 238 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1667) ^ 98 ≠ 1
      reduce_mod_char
      decide

private lemma prime_23339 : Nat.Prime 23339 := by
  apply lucas_from_prime_list 23339 (2 : ZMod 23339) [2,7,1667]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1667
  · decide +kernel
  · change (2 : ZMod 23339) ^ 23338 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 23339) ^ 11669 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 23339) ^ 3334 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 23339) ^ 14 ≠ 1
      reduce_mod_char
      decide

private lemma prime_700171 : Nat.Prime 700171 := by
  apply lucas_from_prime_list 700171 (3 : ZMod 700171) [2,3,5,23339]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23339
  · decide +kernel
  · change (3 : ZMod 700171) ^ 700170 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 700171) ^ 350085 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 700171) ^ 233390 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 700171) ^ 140034 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 700171) ^ 30 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4397 : Nat.Prime 4397 := by
  apply lucas_from_prime_list 4397 (2 : ZMod 4397) [2,2,7,157]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_157
  · decide +kernel
  · change (2 : ZMod 4397) ^ 4396 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4397) ^ 2198 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4397) ^ 2198 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4397) ^ 628 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4397) ^ 28 ≠ 1
      reduce_mod_char
      decide

private lemma prime_79147 : Nat.Prime 79147 := by
  apply lucas_from_prime_list 79147 (2 : ZMod 79147) [2,3,3,4397]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_4397
  · decide +kernel
  · change (2 : ZMod 79147) ^ 79146 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 79147) ^ 39573 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 79147) ^ 26382 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 79147) ^ 26382 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 79147) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_259643 : Nat.Prime 259643 := by
  apply lucas_from_prime_list 259643 (2 : ZMod 259643) [2,131,991]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_991
  · decide +kernel
  · change (2 : ZMod 259643) ^ 259642 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 259643) ^ 129821 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 259643) ^ 1982 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 259643) ^ 262 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999299 : Nat.Prime 3999999999999999299 := by
  apply lucas_from_prime_list 3999999999999999299 (2 : ZMod 3999999999999999299) [2,139,79147,259643,700171]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_79147
    · exact prime_259643
    · exact prime_700171
  · decide +kernel
  · change (2 : ZMod 3999999999999999299) ^ 3999999999999999298 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3999999999999999299) ^ 1999999999999999649 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999299) ^ 28776978417266182 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999299) ^ 50538870708934 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999299) ^ 15405768690086 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999299) ^ 5712890136838 ≠ 1
      reduce_mod_char
      decide

private lemma prime_499 : Nat.Prime 499 := by
  apply lucas_from_prime_list 499 (7 : ZMod 499) [2,3,83]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel
  · change (7 : ZMod 499) ^ 498 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 499) ^ 249 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 499) ^ 166 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 499) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_10979 : Nat.Prime 10979 := by
  apply lucas_from_prime_list 10979 (2 : ZMod 10979) [2,11,499]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_499
  · decide +kernel
  · change (2 : ZMod 10979) ^ 10978 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 10979) ^ 5489 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 10979) ^ 998 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 10979) ^ 22 ≠ 1
      reduce_mod_char
      decide

private lemma prime_911 : Nat.Prime 911 := by
  apply lucas_from_prime_list 911 (17 : ZMod 911) [2,5,7,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel
  · change (17 : ZMod 911) ^ 910 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (17 : ZMod 911) ^ 455 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 911) ^ 182 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 911) ^ 130 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 911) ^ 70 ≠ 1
      reduce_mod_char
      decide

private lemma prime_202243 : Nat.Prime 202243 := by
  apply lucas_from_prime_list 202243 (2 : ZMod 202243) [2,3,37,911]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_911
  · decide +kernel
  · change (2 : ZMod 202243) ^ 202242 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 202243) ^ 101121 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 202243) ^ 67414 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 202243) ^ 5466 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 202243) ^ 222 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3309099967 : Nat.Prime 3309099967 := by
  apply lucas_from_prime_list 3309099967 (3 : ZMod 3309099967) [2,3,3,3,3,101,202243]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_101
    · exact prime_202243
  · decide +kernel
  · change (3 : ZMod 3309099967) ^ 3309099966 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3309099967) ^ 1654549983 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3309099967) ^ 1103033322 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3309099967) ^ 1103033322 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3309099967) ^ 1103033322 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3309099967) ^ 1103033322 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3309099967) ^ 32763366 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3309099967) ^ 16362 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999301 : Nat.Prime 3999999999999999301 := by
  apply lucas_from_prime_list 3999999999999999301 (13 : ZMod 3999999999999999301) [2,2,3,5,5,367,10979,3309099967]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5
    · exact prime_367
    · exact prime_10979
    · exact prime_3309099967
  · decide +kernel
  · change (13 : ZMod 3999999999999999301) ^ 3999999999999999300 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3999999999999999301) ^ 1999999999999999650 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 3999999999999999301) ^ 1999999999999999650 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 3999999999999999301) ^ 1333333333333333100 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 3999999999999999301) ^ 799999999999999860 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 3999999999999999301) ^ 799999999999999860 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 3999999999999999301) ^ 10899182561307900 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 3999999999999999301) ^ 364331906366700 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 3999999999999999301) ^ 1208787900 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2719 : Nat.Prime 2719 := by
  apply lucas_from_prime_list 2719 (3 : ZMod 2719) [2,3,3,151]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_151
  · decide +kernel
  · change (3 : ZMod 2719) ^ 2718 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2719) ^ 1359 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2719) ^ 906 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2719) ^ 906 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2719) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_174017 : Nat.Prime 174017 := by
  apply lucas_from_prime_list 174017 (3 : ZMod 174017) [2,2,2,2,2,2,2719]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2719
  · decide +kernel
  · change (3 : ZMod 174017) ^ 174016 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 174017) ^ 87008 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 174017) ^ 87008 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 174017) ^ 87008 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 174017) ^ 87008 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 174017) ^ 87008 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 174017) ^ 87008 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 174017) ^ 64 ≠ 1
      reduce_mod_char
      decide

private lemma prime_5220511 : Nat.Prime 5220511 := by
  apply lucas_from_prime_list 5220511 (6 : ZMod 5220511) [2,3,5,174017]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_174017
  · decide +kernel
  · change (6 : ZMod 5220511) ^ 5220510 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5220511) ^ 2610255 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 5220511) ^ 1740170 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 5220511) ^ 1044102 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 5220511) ^ 30 ≠ 1
      reduce_mod_char
      decide

private lemma prime_491 : Nat.Prime 491 := by
  apply lucas_from_prime_list 491 (2 : ZMod 491) [2,5,7,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 491) ^ 490 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 491) ^ 245 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 491) ^ 98 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 491) ^ 70 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 491) ^ 70 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999349 : Nat.Prime 3999999999999999349 := by
  apply lucas_from_prime_list 3999999999999999349 (6 : ZMod 3999999999999999349) [2,2,3,3,3,3,3,3,31,61,283,491,5220511]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_31
    · exact prime_61
    · exact prime_283
    · exact prime_491
    · exact prime_5220511
  · decide +kernel
  · change (6 : ZMod 3999999999999999349) ^ 3999999999999999348 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3999999999999999349) ^ 1999999999999999674 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 1999999999999999674 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 1333333333333333116 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 1333333333333333116 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 1333333333333333116 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 1333333333333333116 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 1333333333333333116 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 1333333333333333116 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 129032258064516108 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 65573770491803268 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 14134275618374556 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 8146639511201628 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3999999999999999349) ^ 766208518668 ≠ 1
      reduce_mod_char
      decide

private lemma prime_593 : Nat.Prime 593 := by
  apply lucas_from_prime_list 593 (3 : ZMod 593) [2,2,2,2,37]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_37
  · decide +kernel
  · change (3 : ZMod 593) ^ 592 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 593) ^ 296 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 593) ^ 296 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 593) ^ 296 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 593) ^ 296 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 593) ^ 16 ≠ 1
      reduce_mod_char
      decide

private lemma prime_9613 : Nat.Prime 9613 := by
  apply lucas_from_prime_list 9613 (2 : ZMod 9613) [2,2,3,3,3,89]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_89
  · decide +kernel
  · change (2 : ZMod 9613) ^ 9612 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9613) ^ 4806 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9613) ^ 4806 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9613) ^ 3204 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9613) ^ 3204 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9613) ^ 3204 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9613) ^ 108 ≠ 1
      reduce_mod_char
      decide

private lemma prime_38453 : Nat.Prime 38453 := by
  apply lucas_from_prime_list 38453 (2 : ZMod 38453) [2,2,9613]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_9613
  · decide +kernel
  · change (2 : ZMod 38453) ^ 38452 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 38453) ^ 19226 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 38453) ^ 19226 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 38453) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_724223803 : Nat.Prime 724223803 := by
  apply lucas_from_prime_list 724223803 (7 : ZMod 724223803) [2,3,43,73,38453]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_73
    · exact prime_38453
  · decide +kernel
  · change (7 : ZMod 724223803) ^ 724223802 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 724223803) ^ 362111901 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 724223803) ^ 241407934 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 724223803) ^ 16842414 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 724223803) ^ 9920874 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 724223803) ^ 18834 ≠ 1
      reduce_mod_char
      decide

private lemma prime_649350649350649 : Nat.Prime 649350649350649 := by
  apply lucas_from_prime_list 649350649350649 (17 : ZMod 649350649350649) [2,2,2,3,3,3,7,593,724223803]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_7
    · exact prime_593
    · exact prime_724223803
  · decide +kernel
  · change (17 : ZMod 649350649350649) ^ 649350649350648 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 649350649350649) ^ 324675324675324 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 649350649350649) ^ 324675324675324 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 649350649350649) ^ 324675324675324 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 649350649350649) ^ 216450216450216 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 649350649350649) ^ 216450216450216 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 649350649350649) ^ 216450216450216 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 649350649350649) ^ 92764378478664 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 649350649350649) ^ 1095026390136 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 649350649350649) ^ 896616 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2597402597402597 : Nat.Prime 2597402597402597 := by
  apply lucas_from_prime_list 2597402597402597 (2 : ZMod 2597402597402597) [2,2,649350649350649]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_649350649350649
  · decide +kernel
  · change (2 : ZMod 2597402597402597) ^ 2597402597402596 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 2597402597402597) ^ 1298701298701298 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2597402597402597) ^ 1298701298701298 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2597402597402597) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_36363636363636359 : Nat.Prime 36363636363636359 := by
  apply lucas_from_prime_list 36363636363636359 (7 : ZMod 36363636363636359) [2,7,2597402597402597]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2597402597402597
  · decide +kernel
  · change (7 : ZMod 36363636363636359) ^ 36363636363636358 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 36363636363636359) ^ 18181818181818179 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 36363636363636359) ^ 5194805194805194 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 36363636363636359) ^ 14 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999491 : Nat.Prime 3999999999999999491 := by
  apply lucas_from_prime_list 3999999999999999491 (2 : ZMod 3999999999999999491) [2,5,11,36363636363636359]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_36363636363636359
  · decide +kernel
  · change (2 : ZMod 3999999999999999491) ^ 3999999999999999490 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3999999999999999491) ^ 1999999999999999745 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999491) ^ 799999999999999898 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999491) ^ 363636363636363590 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999491) ^ 110 ≠ 1
      reduce_mod_char
      decide

private lemma prime_883 : Nat.Prime 883 := by
  apply lucas_from_prime_list 883 (2 : ZMod 883) [2,3,3,7,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_7
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 883) ^ 882 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 883) ^ 441 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 883) ^ 294 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 883) ^ 294 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 883) ^ 126 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 883) ^ 126 ≠ 1
      reduce_mod_char
      decide

private lemma prime_401 : Nat.Prime 401 := by
  apply lucas_from_prime_list 401 (3 : ZMod 401) [2,2,2,2,5,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
  · decide +kernel
  · change (3 : ZMod 401) ^ 400 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 401) ^ 200 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 401) ^ 200 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 401) ^ 200 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 401) ^ 200 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 401) ^ 80 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 401) ^ 80 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1579 : Nat.Prime 1579 := by
  apply lucas_from_prime_list 1579 (3 : ZMod 1579) [2,3,263]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
  · decide +kernel
  · change (3 : ZMod 1579) ^ 1578 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 1579) ^ 789 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1579) ^ 526 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1579) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_5548607 : Nat.Prime 5548607 := by
  apply lucas_from_prime_list 5548607 (5 : ZMod 5548607) [2,7,251,1579]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_251
    · exact prime_1579
  · decide +kernel
  · change (5 : ZMod 5548607) ^ 5548606 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5548607) ^ 2774303 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 5548607) ^ 792658 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 5548607) ^ 22106 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 5548607) ^ 3514 ≠ 1
      reduce_mod_char
      decide

private lemma prime_244138709 : Nat.Prime 244138709 := by
  apply lucas_from_prime_list 244138709 (2 : ZMod 244138709) [2,2,11,5548607]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_11
    · exact prime_5548607
  · decide +kernel
  · change (2 : ZMod 244138709) ^ 244138708 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 244138709) ^ 122069354 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 244138709) ^ 122069354 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 244138709) ^ 22194428 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 244138709) ^ 44 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2929664509 : Nat.Prime 2929664509 := by
  apply lucas_from_prime_list 2929664509 (6 : ZMod 2929664509) [2,2,3,244138709]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_244138709
  · decide +kernel
  · change (6 : ZMod 2929664509) ^ 2929664508 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2929664509) ^ 1464832254 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 2929664509) ^ 1464832254 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 2929664509) ^ 976554836 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 2929664509) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_566251415628539 : Nat.Prime 566251415628539 := by
  apply lucas_from_prime_list 566251415628539 (2 : ZMod 566251415628539) [2,241,401,2929664509]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_241
    · exact prime_401
    · exact prime_2929664509
  · decide +kernel
  · change (2 : ZMod 566251415628539) ^ 566251415628538 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 566251415628539) ^ 283125707814269 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 566251415628539) ^ 2349590936218 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 566251415628539) ^ 1412098293338 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 566251415628539) ^ 193282 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999497 : Nat.Prime 3999999999999999497 := by
  apply lucas_from_prime_list 3999999999999999497 (3 : ZMod 3999999999999999497) [2,2,2,883,566251415628539]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_883
    · exact prime_566251415628539
  · decide +kernel
  · change (3 : ZMod 3999999999999999497) ^ 3999999999999999496 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3999999999999999497) ^ 1999999999999999748 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999497) ^ 1999999999999999748 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999497) ^ 1999999999999999748 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999497) ^ 4530011325028312 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999497) ^ 7064 ≠ 1
      reduce_mod_char
      decide

private lemma prime_881 : Nat.Prime 881 := by
  apply lucas_from_prime_list 881 (3 : ZMod 881) [2,2,2,2,5,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_11
  · decide +kernel
  · change (3 : ZMod 881) ^ 880 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 881) ^ 440 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 881) ^ 440 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 881) ^ 440 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 881) ^ 440 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 881) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 881) ^ 80 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4008551 : Nat.Prime 4008551 := by
  apply lucas_from_prime_list 4008551 (14 : ZMod 4008551) [2,5,5,7,13,881]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_881
  · decide +kernel
  · change (14 : ZMod 4008551) ^ 4008550 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 4008551) ^ 2004275 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 4008551) ^ 801710 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 4008551) ^ 801710 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 4008551) ^ 572650 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 4008551) ^ 308350 ≠ 1
      reduce_mod_char
      decide
    · change (14 : ZMod 4008551) ^ 4550 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2693746273 : Nat.Prime 2693746273 := by
  apply lucas_from_prime_list 2693746273 (15 : ZMod 2693746273) [2,2,2,2,2,3,7,4008551]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4008551
  · decide +kernel
  · change (15 : ZMod 2693746273) ^ 2693746272 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 2693746273) ^ 1346873136 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 2693746273) ^ 1346873136 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 2693746273) ^ 1346873136 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 2693746273) ^ 1346873136 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 2693746273) ^ 1346873136 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 2693746273) ^ 897915424 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 2693746273) ^ 384820896 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 2693746273) ^ 672 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1345037 : Nat.Prime 1345037 := by
  apply lucas_from_prime_list 1345037 (3 : ZMod 1345037) [2,2,7,11,11,397]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_11
    · exact prime_397
  · decide +kernel
  · change (3 : ZMod 1345037) ^ 1345036 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1345037) ^ 672518 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1345037) ^ 672518 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1345037) ^ 192148 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1345037) ^ 122276 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1345037) ^ 122276 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1345037) ^ 3388 ≠ 1
      reduce_mod_char
      decide

private lemma prime_999999999999999877 : Nat.Prime 999999999999999877 := by
  apply lucas_from_prime_list 999999999999999877 (5 : ZMod 999999999999999877) [2,2,3,23,1345037,2693746273]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1345037
    · exact prime_2693746273
  · decide +kernel
  · change (5 : ZMod 999999999999999877) ^ 999999999999999876 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 999999999999999877) ^ 499999999999999938 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 999999999999999877) ^ 499999999999999938 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 999999999999999877) ^ 333333333333333292 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 999999999999999877) ^ 43478260869565212 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 999999999999999877) ^ 743473971348 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 999999999999999877) ^ 371230212 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999509 : Nat.Prime 3999999999999999509 := by
  apply lucas_from_prime_list 3999999999999999509 (2 : ZMod 3999999999999999509) [2,2,999999999999999877]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_999999999999999877
  · decide +kernel
  · change (2 : ZMod 3999999999999999509) ^ 3999999999999999508 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 3999999999999999509) ^ 1999999999999999754 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999509) ^ 1999999999999999754 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999509) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1301 : Nat.Prime 1301 := by
  apply lucas_from_prime_list 1301 (2 : ZMod 1301) [2,2,5,5,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_13
  · decide +kernel
  · change (2 : ZMod 1301) ^ 1300 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1301) ^ 650 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1301) ^ 650 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1301) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1301) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1301) ^ 100 ≠ 1
      reduce_mod_char
      decide

private lemma prime_124897 : Nat.Prime 124897 := by
  apply lucas_from_prime_list 124897 (5 : ZMod 124897) [2,2,2,2,2,3,1301]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_1301
  · decide +kernel
  · change (5 : ZMod 124897) ^ 124896 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 124897) ^ 62448 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 124897) ^ 62448 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 124897) ^ 62448 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 124897) ^ 62448 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 124897) ^ 62448 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 124897) ^ 41632 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 124897) ^ 96 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2287 : Nat.Prime 2287 := by
  apply lucas_from_prime_list 2287 (19 : ZMod 2287) [2,3,3,127]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_127
  · decide +kernel
  · change (19 : ZMod 2287) ^ 2286 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (19 : ZMod 2287) ^ 1143 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 2287) ^ 762 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 2287) ^ 762 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 2287) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_757 : Nat.Prime 757 := by
  apply lucas_from_prime_list 757 (2 : ZMod 757) [2,2,3,3,3,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 757) ^ 756 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 757) ^ 378 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 757) ^ 378 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 757) ^ 252 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 757) ^ 252 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 757) ^ 252 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 757) ^ 108 ≠ 1
      reduce_mod_char
      decide

private lemma prime_12177103 : Nat.Prime 12177103 := by
  apply lucas_from_prime_list 12177103 (29 : ZMod 12177103) [2,3,7,383,757]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_383
    · exact prime_757
  · decide +kernel
  · change (29 : ZMod 12177103) ^ 12177102 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 12177103) ^ 6088551 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 12177103) ^ 4059034 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 12177103) ^ 1739586 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 12177103) ^ 31794 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 12177103) ^ 16086 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999551 : Nat.Prime 3999999999999999551 := by
  apply lucas_from_prime_list 3999999999999999551 (19 : ZMod 3999999999999999551) [2,5,5,23,2287,124897,12177103]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_23
    · exact prime_2287
    · exact prime_124897
    · exact prime_12177103
  · decide +kernel
  · change (19 : ZMod 3999999999999999551) ^ 3999999999999999550 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 3999999999999999551) ^ 1999999999999999775 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999999551) ^ 799999999999999910 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999999551) ^ 799999999999999910 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999999551) ^ 173913043478260850 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999999551) ^ 1749016178399650 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999999551) ^ 32026389745150 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 3999999999999999551) ^ 328485354850 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1997 : Nat.Prime 1997 := by
  apply lucas_from_prime_list 1997 (2 : ZMod 1997) [2,2,499]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_499
  · decide +kernel
  · change (2 : ZMod 1997) ^ 1996 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 1997) ^ 998 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1997) ^ 998 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1997) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_40961 : Nat.Prime 40961 := by
  apply lucas_from_prime_list 40961 (3 : ZMod 40961) [2,2,2,2,2,2,2,2,2,2,2,2,2,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
  · decide +kernel
  · change (3 : ZMod 40961) ^ 40960 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 20480 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 40961) ^ 8192 ≠ 1
      reduce_mod_char
      decide

private lemma prime_327689 : Nat.Prime 327689 := by
  apply lucas_from_prime_list 327689 (3 : ZMod 327689) [2,2,2,40961]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_40961
  · decide +kernel
  · change (3 : ZMod 327689) ^ 327688 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 327689) ^ 163844 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 327689) ^ 163844 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 327689) ^ 163844 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 327689) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_655379 : Nat.Prime 655379 := by
  apply lucas_from_prime_list 655379 (2 : ZMod 655379) [2,327689]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_327689
  · decide +kernel
  · change (2 : ZMod 655379) ^ 655378 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 655379) ^ 327689 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 655379) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_32117 : Nat.Prime 32117 := by
  apply lucas_from_prime_list 32117 (2 : ZMod 32117) [2,2,7,31,37]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_37
  · decide +kernel
  · change (2 : ZMod 32117) ^ 32116 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32117) ^ 16058 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 32117) ^ 16058 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 32117) ^ 4588 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 32117) ^ 1036 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 32117) ^ 868 ≠ 1
      reduce_mod_char
      decide

private lemma prime_7703863487539 : Nat.Prime 7703863487539 := by
  apply lucas_from_prime_list 7703863487539 (3 : ZMod 7703863487539) [2,3,61,32117,655379]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_32117
    · exact prime_655379
  · decide +kernel
  · change (3 : ZMod 7703863487539) ^ 7703863487538 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7703863487539) ^ 3851931743769 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 7703863487539) ^ 2567954495846 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 7703863487539) ^ 126292844058 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 7703863487539) ^ 239868714 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 7703863487539) ^ 11754822 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999581 : Nat.Prime 3999999999999999581 := by
  apply lucas_from_prime_list 3999999999999999581 (7 : ZMod 3999999999999999581) [2,2,5,13,1997,7703863487539]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1997
    · exact prime_7703863487539
  · decide +kernel
  · change (7 : ZMod 3999999999999999581) ^ 3999999999999999580 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3999999999999999581) ^ 1999999999999999790 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999581) ^ 1999999999999999790 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999581) ^ 799999999999999916 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999581) ^ 307692307692307660 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999581) ^ 2003004506760140 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999581) ^ 519220 ≠ 1
      reduce_mod_char
      decide

private lemma prime_18913 : Nat.Prime 18913 := by
  apply lucas_from_prime_list 18913 (7 : ZMod 18913) [2,2,2,2,2,3,197]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_197
  · decide +kernel
  · change (7 : ZMod 18913) ^ 18912 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18913) ^ 9456 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 18913) ^ 9456 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 18913) ^ 9456 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 18913) ^ 9456 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 18913) ^ 9456 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 18913) ^ 6304 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 18913) ^ 96 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1283 : Nat.Prime 1283 := by
  apply lucas_from_prime_list 1283 (2 : ZMod 1283) [2,641]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_641
  · decide +kernel
  · change (2 : ZMod 1283) ^ 1282 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 1283) ^ 641 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1283) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_115471 : Nat.Prime 115471 := by
  apply lucas_from_prime_list 115471 (6 : ZMod 115471) [2,3,3,5,1283]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_1283
  · decide +kernel
  · change (6 : ZMod 115471) ^ 115470 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 115471) ^ 57735 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 115471) ^ 38490 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 115471) ^ 38490 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 115471) ^ 23094 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 115471) ^ 90 ≠ 1
      reduce_mod_char
      decide

private lemma prime_37379684141669 : Nat.Prime 37379684141669 := by
  apply lucas_from_prime_list 37379684141669 (2 : ZMod 37379684141669) [2,2,11,389,18913,115471]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_11
    · exact prime_389
    · exact prime_18913
    · exact prime_115471
  · decide +kernel
  · change (2 : ZMod 37379684141669) ^ 37379684141668 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37379684141669) ^ 18689842070834 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37379684141669) ^ 18689842070834 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37379684141669) ^ 3398153103788 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37379684141669) ^ 96091733012 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37379684141669) ^ 1976401636 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37379684141669) ^ 323714908 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999691 : Nat.Prime 3999999999999999691 := by
  apply lucas_from_prime_list 3999999999999999691 (3 : ZMod 3999999999999999691) [2,3,3,5,29,41,37379684141669]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_41
    · exact prime_37379684141669
  · decide +kernel
  · change (3 : ZMod 3999999999999999691) ^ 3999999999999999690 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3999999999999999691) ^ 1999999999999999845 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999691) ^ 1333333333333333230 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999691) ^ 1333333333333333230 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999691) ^ 799999999999999938 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999691) ^ 137931034482758610 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999691) ^ 97560975609756090 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3999999999999999691) ^ 107010 ≠ 1
      reduce_mod_char
      decide

private lemma prime_14407 : Nat.Prime 14407 := by
  apply lucas_from_prime_list 14407 (19 : ZMod 14407) [2,3,7,7,7,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7
    · exact prime_7
    · exact prime_7
  · decide +kernel
  · change (19 : ZMod 14407) ^ 14406 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 14407) ^ 7203 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 14407) ^ 4802 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 14407) ^ 2058 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 14407) ^ 2058 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 14407) ^ 2058 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 14407) ^ 2058 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1786469 : Nat.Prime 1786469 := by
  apply lucas_from_prime_list 1786469 (2 : ZMod 1786469) [2,2,31,14407]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_31
    · exact prime_14407
  · decide +kernel
  · change (2 : ZMod 1786469) ^ 1786468 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1786469) ^ 893234 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1786469) ^ 893234 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1786469) ^ 57628 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1786469) ^ 124 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3572939 : Nat.Prime 3572939 := by
  apply lucas_from_prime_list 3572939 (2 : ZMod 3572939) [2,1786469]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_1786469
  · decide +kernel
  · change (2 : ZMod 3572939) ^ 3572938 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 3572939) ^ 1786469 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3572939) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4093 : Nat.Prime 4093 := by
  apply lucas_from_prime_list 4093 (2 : ZMod 4093) [2,2,3,11,31]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
  · decide +kernel
  · change (2 : ZMod 4093) ^ 4092 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4093) ^ 2046 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4093) ^ 2046 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4093) ^ 1364 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4093) ^ 372 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4093) ^ 132 ≠ 1
      reduce_mod_char
      decide

private lemma prime_777448979 : Nat.Prime 777448979 := by
  apply lucas_from_prime_list 777448979 (2 : ZMod 777448979) [2,73,1301,4093]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_1301
    · exact prime_4093
  · decide +kernel
  · change (2 : ZMod 777448979) ^ 777448978 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 777448979) ^ 388724489 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 777448979) ^ 10649986 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 777448979) ^ 597578 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 777448979) ^ 189946 ≠ 1
      reduce_mod_char
      decide

private lemma prime_13994081623 : Nat.Prime 13994081623 := by
  apply lucas_from_prime_list 13994081623 (3 : ZMod 13994081623) [2,3,3,777448979]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_777448979
  · decide +kernel
  · change (3 : ZMod 13994081623) ^ 13994081622 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13994081623) ^ 6997040811 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 13994081623) ^ 4664693874 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 13994081623) ^ 4664693874 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 13994081623) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999761 : Nat.Prime 3999999999999999761 := by
  apply lucas_from_prime_list 3999999999999999761 (7 : ZMod 3999999999999999761) [2,2,2,2,5,3572939,13994081623]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_3572939
    · exact prime_13994081623
  · decide +kernel
  · change (7 : ZMod 3999999999999999761) ^ 3999999999999999760 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3999999999999999761) ^ 1999999999999999880 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999761) ^ 1999999999999999880 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999761) ^ 1999999999999999880 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999761) ^ 1999999999999999880 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999761) ^ 799999999999999952 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999761) ^ 1119526529840 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3999999999999999761) ^ 285835120 ≠ 1
      reduce_mod_char
      decide

private lemma prime_239851 : Nat.Prime 239851 := by
  apply lucas_from_prime_list 239851 (3 : ZMod 239851) [2,3,3,5,5,13,41]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_5
    · exact prime_13
    · exact prime_41
  · decide +kernel
  · change (3 : ZMod 239851) ^ 239850 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 239851) ^ 119925 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 239851) ^ 79950 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 239851) ^ 79950 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 239851) ^ 47970 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 239851) ^ 47970 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 239851) ^ 18450 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 239851) ^ 5850 ≠ 1
      reduce_mod_char
      decide

private lemma prime_265157 : Nat.Prime 265157 := by
  apply lucas_from_prime_list 265157 (2 : ZMod 265157) [2,2,151,439]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_151
    · exact prime_439
  · decide +kernel
  · change (2 : ZMod 265157) ^ 265156 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 265157) ^ 132578 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 265157) ^ 132578 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 265157) ^ 1756 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 265157) ^ 604 ≠ 1
      reduce_mod_char
      decide

private lemma prime_6363769 : Nat.Prime 6363769 := by
  apply lucas_from_prime_list 6363769 (7 : ZMod 6363769) [2,2,2,3,265157]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_265157
  · decide +kernel
  · change (7 : ZMod 6363769) ^ 6363768 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6363769) ^ 3181884 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 6363769) ^ 3181884 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 6363769) ^ 3181884 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 6363769) ^ 2121256 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 6363769) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999999979 : Nat.Prime 399999999999999979 := by
  apply lucas_from_prime_list 399999999999999979 (2 : ZMod 399999999999999979) [2,3,3,3,23,211,239851,6363769]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_23
    · exact prime_211
    · exact prime_239851
    · exact prime_6363769
  · decide +kernel
  · change (2 : ZMod 399999999999999979) ^ 399999999999999978 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999999999979) ^ 199999999999999989 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999999979) ^ 133333333333333326 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999999979) ^ 133333333333333326 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999999979) ^ 133333333333333326 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999999979) ^ 17391304347826086 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999999979) ^ 1895734597156398 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999999979) ^ 1667702031678 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999999979) ^ 62855832762 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999791 : Nat.Prime 3999999999999999791 := by
  apply lucas_from_prime_list 3999999999999999791 (11 : ZMod 3999999999999999791) [2,5,399999999999999979]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_399999999999999979
  · decide +kernel
  · change (11 : ZMod 3999999999999999791) ^ 3999999999999999790 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (11 : ZMod 3999999999999999791) ^ 1999999999999999895 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3999999999999999791) ^ 799999999999999958 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3999999999999999791) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_547 : Nat.Prime 547 := by
  apply lucas_from_prime_list 547 (2 : ZMod 547) [2,3,7,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel
  · change (2 : ZMod 547) ^ 546 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 547) ^ 273 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 547) ^ 182 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 547) ^ 78 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 547) ^ 42 ≠ 1
      reduce_mod_char
      decide

private lemma prime_20681 : Nat.Prime 20681 := by
  apply lucas_from_prime_list 20681 (3 : ZMod 20681) [2,2,2,5,11,47]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_47
  · decide +kernel
  · change (3 : ZMod 20681) ^ 20680 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20681) ^ 10340 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 20681) ^ 10340 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 20681) ^ 10340 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 20681) ^ 4136 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 20681) ^ 1880 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 20681) ^ 440 ≠ 1
      reduce_mod_char
      decide

private lemma prime_15924371 : Nat.Prime 15924371 := by
  apply lucas_from_prime_list 15924371 (2 : ZMod 15924371) [2,5,7,11,20681]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_20681
  · decide +kernel
  · change (2 : ZMod 15924371) ^ 15924370 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15924371) ^ 7962185 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 15924371) ^ 3184874 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 15924371) ^ 2274910 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 15924371) ^ 1447670 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 15924371) ^ 770 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1069 : Nat.Prime 1069 := by
  apply lucas_from_prime_list 1069 (6 : ZMod 1069) [2,2,3,89]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · decide +kernel
  · change (6 : ZMod 1069) ^ 1068 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1069) ^ 534 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 1069) ^ 534 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 1069) ^ 356 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 1069) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_25657 : Nat.Prime 25657 := by
  apply lucas_from_prime_list 25657 (5 : ZMod 25657) [2,2,2,3,1069]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_1069
  · decide +kernel
  · change (5 : ZMod 25657) ^ 25656 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25657) ^ 12828 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 25657) ^ 12828 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 25657) ^ 12828 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 25657) ^ 8552 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 25657) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999883 : Nat.Prime 3999999999999999883 := by
  apply lucas_from_prime_list 3999999999999999883 (2 : ZMod 3999999999999999883) [2,3,19,157,547,25657,15924371]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_157
    · exact prime_547
    · exact prime_25657
    · exact prime_15924371
  · decide +kernel
  · change (2 : ZMod 3999999999999999883) ^ 3999999999999999882 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3999999999999999883) ^ 1999999999999999941 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999883) ^ 1333333333333333294 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999883) ^ 210526315789473678 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999883) ^ 25477707006369426 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999883) ^ 7312614259597806 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999883) ^ 155902872510426 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3999999999999999883) ^ 251187315342 ≠ 1
      reduce_mod_char
      decide

private lemma prime_6421 : Nat.Prime 6421 := by
  apply lucas_from_prime_list 6421 (6 : ZMod 6421) [2,2,3,5,107]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
  · decide +kernel
  · change (6 : ZMod 6421) ^ 6420 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6421) ^ 3210 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 6421) ^ 3210 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 6421) ^ 2140 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 6421) ^ 1284 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 6421) ^ 60 ≠ 1
      reduce_mod_char
      decide

private lemma prime_192631 : Nat.Prime 192631 := by
  apply lucas_from_prime_list 192631 (3 : ZMod 192631) [2,3,5,6421]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6421
  · decide +kernel
  · change (3 : ZMod 192631) ^ 192630 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 192631) ^ 96315 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 192631) ^ 64210 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 192631) ^ 38526 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 192631) ^ 30 ≠ 1
      reduce_mod_char
      decide

private lemma prime_947 : Nat.Prime 947 := by
  apply lucas_from_prime_list 947 (2 : ZMod 947) [2,11,43]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
  · decide +kernel
  · change (2 : ZMod 947) ^ 946 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 947) ^ 473 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 947) ^ 86 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 947) ^ 22 ≠ 1
      reduce_mod_char
      decide

private lemma prime_7577 : Nat.Prime 7577 := by
  apply lucas_from_prime_list 7577 (3 : ZMod 7577) [2,2,2,947]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_947
  · decide +kernel
  · change (3 : ZMod 7577) ^ 7576 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7577) ^ 3788 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 7577) ^ 3788 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 7577) ^ 3788 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 7577) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4318891 : Nat.Prime 4318891 := by
  apply lucas_from_prime_list 4318891 (2 : ZMod 4318891) [2,3,5,19,7577]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_7577
  · decide +kernel
  · change (2 : ZMod 4318891) ^ 4318890 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4318891) ^ 2159445 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4318891) ^ 1439630 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4318891) ^ 863778 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4318891) ^ 227310 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4318891) ^ 570 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2712263549 : Nat.Prime 2712263549 := by
  apply lucas_from_prime_list 2712263549 (2 : ZMod 2712263549) [2,2,157,4318891]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_157
    · exact prime_4318891
  · decide +kernel
  · change (2 : ZMod 2712263549) ^ 2712263548 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2712263549) ^ 1356131774 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2712263549) ^ 1356131774 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2712263549) ^ 17275564 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2712263549) ^ 628 ≠ 1
      reduce_mod_char
      decide

private lemma prime_181818181818181813 : Nat.Prime 181818181818181813 := by
  apply lucas_from_prime_list 181818181818181813 (5 : ZMod 181818181818181813) [2,2,3,29,192631,2712263549]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_192631
    · exact prime_2712263549
  · decide +kernel
  · change (5 : ZMod 181818181818181813) ^ 181818181818181812 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 181818181818181813) ^ 90909090909090906 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 181818181818181813) ^ 90909090909090906 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 181818181818181813) ^ 60606060606060604 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 181818181818181813) ^ 6269592476489028 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 181818181818181813) ^ 943867715052 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 181818181818181813) ^ 67035588 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3999999999999999887 : Nat.Prime 3999999999999999887 := by
  apply lucas_from_prime_list 3999999999999999887 (5 : ZMod 3999999999999999887) [2,11,181818181818181813]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_181818181818181813
  · decide +kernel
  · change (5 : ZMod 3999999999999999887) ^ 3999999999999999886 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 3999999999999999887) ^ 1999999999999999943 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999999887) ^ 363636363636363626 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3999999999999999887) ^ 22 ≠ 1
      reduce_mod_char
      decide

end GoldbachLucasSegmentPrimes

namespace GoldbachLucasBitmapData3999999999999999000_4000000000000000000
open GoldbachCertificate GoldbachBitmapCertificate

private def primes : PrimeTree := (.node 337 (.node 139 (.node 61 (.node 29 (.node 13 (.node 7 (.node 5 (.node 3 .empty .empty) .empty) (.node 11 .empty .empty)) (.node 19 (.node 17 .empty .empty) (.node 23 .empty .empty))) (.node 43 (.node 37 (.node 31 .empty .empty) (.node 41 .empty .empty)) (.node 53 (.node 47 .empty .empty) (.node 59 .empty .empty)))) (.node 101 (.node 79 (.node 71 (.node 67 .empty .empty) (.node 73 .empty .empty)) (.node 89 (.node 83 .empty .empty) (.node 97 .empty .empty))) (.node 113 (.node 107 (.node 103 .empty .empty) (.node 109 .empty .empty)) (.node 131 (.node 127 .empty .empty) (.node 137 .empty .empty))))) (.node 233 (.node 191 (.node 167 (.node 157 (.node 151 (.node 149 .empty .empty) .empty) (.node 163 .empty .empty)) (.node 179 (.node 173 .empty .empty) (.node 181 .empty .empty))) (.node 211 (.node 197 (.node 193 .empty .empty) (.node 199 .empty .empty)) (.node 227 (.node 223 .empty .empty) (.node 229 .empty .empty)))) (.node 277 (.node 257 (.node 241 (.node 239 .empty .empty) (.node 251 .empty .empty)) (.node 269 (.node 263 .empty .empty) (.node 271 .empty .empty))) (.node 307 (.node 283 (.node 281 .empty .empty) (.node 293 .empty .empty)) (.node 317 (.node 313 .empty .empty) (.node 331 .empty .empty)))))) (.node 733 (.node 443 (.node 389 (.node 367 (.node 353 (.node 349 (.node 347 .empty .empty) .empty) (.node 359 .empty .empty)) (.node 379 (.node 373 .empty .empty) (.node 383 .empty .empty))) (.node 421 (.node 409 (.node 397 .empty .empty) (.node 419 .empty .empty)) (.node 433 (.node 431 .empty .empty) (.node 439 .empty .empty)))) (.node 521 (.node 463 (.node 457 (.node 449 .empty .empty) (.node 461 .empty .empty)) (.node 487 (.node 467 .empty .empty) (.node 509 .empty .empty))) (.node 607 (.node 557 (.node 523 .empty .empty) (.node 577 .empty .empty)) (.node 641 (.node 617 .empty .empty) (.node 643 .empty .empty))))) (.node 3999999999999998941 (.node 3999999999999998689 (.node 997 (.node 853 (.node 751 .empty .empty) (.node 919 .empty .empty)) (.node 1129 (.node 1087 .empty .empty) (.node 3999999999999998341 .empty .empty))) (.node 3999999999999998803 (.node 3999999999999998749 (.node 3999999999999998711 .empty .empty) (.node 3999999999999998777 .empty .empty)) (.node 3999999999999998833 (.node 3999999999999998807 .empty .empty) (.node 3999999999999998867 .empty .empty)))) (.node 3999999999999999509 (.node 3999999999999999301 (.node 3999999999999999223 (.node 3999999999999999011 .empty .empty) (.node 3999999999999999299 .empty .empty)) (.node 3999999999999999491 (.node 3999999999999999349 .empty .empty) (.node 3999999999999999497 .empty .empty))) (.node 3999999999999999761 (.node 3999999999999999581 (.node 3999999999999999551 .empty .empty) (.node 3999999999999999691 .empty .empty)) (.node 3999999999999999883 (.node 3999999999999999791 .empty .empty) (.node 3999999999999999887 .empty .empty)))))))
private def left : List ℕ := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,313,317,331,337,347,349,353,359,367,373,379,383,389,397,409,419,421,431,433,439,443,449,457,461,463,467,487,509,521,523,557,577,607,617,641,643,733,751,853,919,997,1087,1129]

private lemma primes_valid : primes.check = true := by
  simp [primes, PrimeTree.check, GoldbachCertificate.primeCheck_spec, GoldbachLucasSegmentPrimes.prime_3, GoldbachLucasSegmentPrimes.prime_5, GoldbachLucasSegmentPrimes.prime_7, GoldbachLucasSegmentPrimes.prime_11, GoldbachLucasSegmentPrimes.prime_13, GoldbachLucasSegmentPrimes.prime_17, GoldbachLucasSegmentPrimes.prime_19, GoldbachLucasSegmentPrimes.prime_23, GoldbachLucasSegmentPrimes.prime_29, GoldbachLucasSegmentPrimes.prime_31, GoldbachLucasSegmentPrimes.prime_37, GoldbachLucasSegmentPrimes.prime_41, GoldbachLucasSegmentPrimes.prime_43, GoldbachLucasSegmentPrimes.prime_47, GoldbachLucasSegmentPrimes.prime_53, GoldbachLucasSegmentPrimes.prime_59, GoldbachLucasSegmentPrimes.prime_61, GoldbachLucasSegmentPrimes.prime_67, GoldbachLucasSegmentPrimes.prime_71, GoldbachLucasSegmentPrimes.prime_73, GoldbachLucasSegmentPrimes.prime_79, GoldbachLucasSegmentPrimes.prime_83, GoldbachLucasSegmentPrimes.prime_89, GoldbachLucasSegmentPrimes.prime_97, GoldbachLucasSegmentPrimes.prime_101, GoldbachLucasSegmentPrimes.prime_103, GoldbachLucasSegmentPrimes.prime_107, GoldbachLucasSegmentPrimes.prime_109, GoldbachLucasSegmentPrimes.prime_113, GoldbachLucasSegmentPrimes.prime_127, GoldbachLucasSegmentPrimes.prime_131, GoldbachLucasSegmentPrimes.prime_137, GoldbachLucasSegmentPrimes.prime_139, GoldbachLucasSegmentPrimes.prime_149, GoldbachLucasSegmentPrimes.prime_151, GoldbachLucasSegmentPrimes.prime_157, GoldbachLucasSegmentPrimes.prime_163, GoldbachLucasSegmentPrimes.prime_167, GoldbachLucasSegmentPrimes.prime_173, GoldbachLucasSegmentPrimes.prime_179, GoldbachLucasSegmentPrimes.prime_181, GoldbachLucasSegmentPrimes.prime_191, GoldbachLucasSegmentPrimes.prime_193, GoldbachLucasSegmentPrimes.prime_197, GoldbachLucasSegmentPrimes.prime_199, GoldbachLucasSegmentPrimes.prime_211, GoldbachLucasSegmentPrimes.prime_223, GoldbachLucasSegmentPrimes.prime_227, GoldbachLucasSegmentPrimes.prime_229, GoldbachLucasSegmentPrimes.prime_233, GoldbachLucasSegmentPrimes.prime_239, GoldbachLucasSegmentPrimes.prime_241, GoldbachLucasSegmentPrimes.prime_251, GoldbachLucasSegmentPrimes.prime_257, GoldbachLucasSegmentPrimes.prime_263, GoldbachLucasSegmentPrimes.prime_269, GoldbachLucasSegmentPrimes.prime_271, GoldbachLucasSegmentPrimes.prime_277, GoldbachLucasSegmentPrimes.prime_281, GoldbachLucasSegmentPrimes.prime_283, GoldbachLucasSegmentPrimes.prime_293, GoldbachLucasSegmentPrimes.prime_307, GoldbachLucasSegmentPrimes.prime_313, GoldbachLucasSegmentPrimes.prime_317, GoldbachLucasSegmentPrimes.prime_331, GoldbachLucasSegmentPrimes.prime_337, GoldbachLucasSegmentPrimes.prime_347, GoldbachLucasSegmentPrimes.prime_349, GoldbachLucasSegmentPrimes.prime_353, GoldbachLucasSegmentPrimes.prime_359, GoldbachLucasSegmentPrimes.prime_367, GoldbachLucasSegmentPrimes.prime_373, GoldbachLucasSegmentPrimes.prime_379, GoldbachLucasSegmentPrimes.prime_383, GoldbachLucasSegmentPrimes.prime_389, GoldbachLucasSegmentPrimes.prime_397, GoldbachLucasSegmentPrimes.prime_409, GoldbachLucasSegmentPrimes.prime_419, GoldbachLucasSegmentPrimes.prime_421, GoldbachLucasSegmentPrimes.prime_431, GoldbachLucasSegmentPrimes.prime_433, GoldbachLucasSegmentPrimes.prime_439, GoldbachLucasSegmentPrimes.prime_443, GoldbachLucasSegmentPrimes.prime_449, GoldbachLucasSegmentPrimes.prime_457, GoldbachLucasSegmentPrimes.prime_461, GoldbachLucasSegmentPrimes.prime_463, GoldbachLucasSegmentPrimes.prime_467, GoldbachLucasSegmentPrimes.prime_487, GoldbachLucasSegmentPrimes.prime_509, GoldbachLucasSegmentPrimes.prime_521, GoldbachLucasSegmentPrimes.prime_523, GoldbachLucasSegmentPrimes.prime_557, GoldbachLucasSegmentPrimes.prime_577, GoldbachLucasSegmentPrimes.prime_607, GoldbachLucasSegmentPrimes.prime_617, GoldbachLucasSegmentPrimes.prime_641, GoldbachLucasSegmentPrimes.prime_643, GoldbachLucasSegmentPrimes.prime_733, GoldbachLucasSegmentPrimes.prime_751, GoldbachLucasSegmentPrimes.prime_853, GoldbachLucasSegmentPrimes.prime_919, GoldbachLucasSegmentPrimes.prime_997, GoldbachLucasSegmentPrimes.prime_1087, GoldbachLucasSegmentPrimes.prime_1129, GoldbachLucasSegmentPrimes.prime_3999999999999998341, GoldbachLucasSegmentPrimes.prime_3999999999999998689, GoldbachLucasSegmentPrimes.prime_3999999999999998711, GoldbachLucasSegmentPrimes.prime_3999999999999998749, GoldbachLucasSegmentPrimes.prime_3999999999999998777, GoldbachLucasSegmentPrimes.prime_3999999999999998803, GoldbachLucasSegmentPrimes.prime_3999999999999998807, GoldbachLucasSegmentPrimes.prime_3999999999999998833, GoldbachLucasSegmentPrimes.prime_3999999999999998867, GoldbachLucasSegmentPrimes.prime_3999999999999998941, GoldbachLucasSegmentPrimes.prime_3999999999999999011, GoldbachLucasSegmentPrimes.prime_3999999999999999223, GoldbachLucasSegmentPrimes.prime_3999999999999999299, GoldbachLucasSegmentPrimes.prime_3999999999999999301, GoldbachLucasSegmentPrimes.prime_3999999999999999349, GoldbachLucasSegmentPrimes.prime_3999999999999999491, GoldbachLucasSegmentPrimes.prime_3999999999999999497, GoldbachLucasSegmentPrimes.prime_3999999999999999509, GoldbachLucasSegmentPrimes.prime_3999999999999999551, GoldbachLucasSegmentPrimes.prime_3999999999999999581, GoldbachLucasSegmentPrimes.prime_3999999999999999691, GoldbachLucasSegmentPrimes.prime_3999999999999999761, GoldbachLucasSegmentPrimes.prime_3999999999999999791, GoldbachLucasSegmentPrimes.prime_3999999999999999883, GoldbachLucasSegmentPrimes.prime_3999999999999999887]

private lemma left_valid : leftCheck 5569 primes left = true := by decide +kernel
private lemma coverage_valid : covers 1999999999999996715 2785 501 primes left = true := by decide +kernel

end GoldbachLucasBitmapData3999999999999999000_4000000000000000000

theorem solution (n : ℕ) (hlo : 3999999999999999000 ≤ n) (hhi : n ≤ 4000000000000000000) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ 5569 ∧ n = p + q := by
  exact GoldbachBitmapCertificate.block_sound 1999999999999996715 2785 501 5569
    GoldbachLucasBitmapData3999999999999999000_4000000000000000000.primes GoldbachLucasBitmapData3999999999999999000_4000000000000000000.left GoldbachLucasBitmapData3999999999999999000_4000000000000000000.primes_valid
    GoldbachLucasBitmapData3999999999999999000_4000000000000000000.left_valid GoldbachLucasBitmapData3999999999999999000_4000000000000000000.coverage_valid n (by omega) (by omega) he

#print axioms solution
