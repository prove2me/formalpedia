-- Prove2me | solution 1 for ProofsInTheBook.Chapter04.ZagierTriple.exists_sq_add_sq_of_prime_mod_four_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T14:43:29.147329+00:00
-- url     : https://prove2.me/submissions/eae7de3b-232d-416a-a0b6-a7bb467d108e

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter04


/-!
# Chapter 4: Representing numbers as sums of two squares

From "Proofs from THE BOOK":

**Fermat's two-squares theorem**: An odd prime p is a sum of two squares
iff p ≡ 1 (mod 4).

The book gives Zagier's celebrated "one-sentence proof" via an involution
on S = {(x,y,z) ∈ ℕ₊³ : x² + 4yz = p}, plus the general characterization:
n is a sum of two squares iff every prime factor p ≡ 3 (mod 4) of n
occurs to an even power.
-/

namespace ProofsInTheBook.Chapter04

open Nat

/-!
### Necessity: p ≡ 3 (mod 4) implies p is NOT a sum of two squares

*Book proof.* Squares mod 4 are 0 or 1, so a² + b² mod 4 ∈ {0, 1, 2}.
Hence a² + b² ≢ 3 (mod 4).
-/





/-!
### Brahmagupta–Fibonacci identity

The set of sums of two squares is closed under multiplication:
  (a² + b²)(c² + d²) = (ac - bd)² + (ad + bc)².

This is a key tool: once we know primes ≡ 1 (mod 4) are sums of two squares,
we can represent any product of such primes.
-/



theorem exists_fixed_of_odd_card_involutive {α : Type*} [Fintype α]
    (e : Equiv.Perm α) (hodd : Odd (Fintype.card α)) (hinv : e ^ 2 = 1) :
    ∃ x : α, e x = x := by
  classical
  by_contra hnone
  have hsupp : e.support = Finset.univ := by
    ext x
    have hx : e x ≠ x := fun hfix => hnone ⟨x, hfix⟩
    simp [Equiv.Perm.mem_support, hx]
  have htwo : 2 ∣ Fintype.card α := by
    simpa [hsupp] using Equiv.Perm.two_dvd_card_support (σ := e) hinv
  exact hodd.not_two_dvd_nat htwo

theorem odd_card_of_involutive_unique_fixed {α : Type*} [Fintype α] [DecidableEq α]
    (f : Function.End α) (hinv : Function.Involutive f)
    (huniq : ∃! x : α, f x = x) : Odd (Fintype.card α) := by
  have hf2 : f ^ 2 = 1 := by
    apply funext
    intro x
    exact hinv x
  have hf : f ^ 2 ^ 1 = 1 := by
    simpa using hf2
  have hmod : Fintype.card α ≡ Fintype.card (Function.fixedPoints f) [MOD 2] := by
    simpa using Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf
  have hfixed : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    rcases huniq with ⟨x, hx, hunique⟩
    exact ⟨⟨x, hx⟩, fun y => Subtype.ext (hunique y y.property)⟩
  rw [hfixed] at hmod
  rw [Nat.odd_iff]
  exact hmod

/-!
### Sufficiency: primes p ≡ 1 (mod 4) are sums of two squares

The book presents Zagier's proof: Consider the finite set
  S = {(x, y, z) ∈ ℕ₊³ : x² + 4yz = p}.
Define the involution
  f(x, y, z) = (x + 2z, z, y - x - z)  if x < y - z,
             = (2y - x, y, x - y + z)   if y - z < x < 2y,
             = (x - 2y, x - y + z, y)   if x > 2y.
This involution has exactly one fixed point (1, 1, (p-1)/4), so |S| is odd.
The involution g(x,y,z) = (x,z,y) also acts on S. Since |S| is odd,
g must have a fixed point (x,y,y), giving x² + 4y² = p.

The formalization below follows this path: it builds the finite triple type,
the three branches of Zagier's involution, the unique fixed point, the parity
step, and then the swap fixed-point argument.
-/



namespace ZagierTriple

@[ext] theorem ext {p : ℕ} {a b : ZagierTriple p}
    (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a
  cases b
  simp at hx hy hz
  subst hx
  subst hy
  subst hz
  rfl



























theorem zagierMap_branchOne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) (h : t.x.val < t.y.val - t.z.val) :
    zagierMapOfPrimeNeTwo hp hp2 (branchOne t h) = t := by
  have h1raw : ¬ t.x.val + 2 * t.z.val < t.z.val - (t.y.val - t.x.val - t.z.val) := by
    omega
  have h2raw : ¬ t.x.val + 2 * t.z.val < 2 * t.z.val := by
    omega
  ext
  all_goals simp [zagierMapOfPrimeNeTwo, branchOne, branchThree, h1raw, h2raw]
  all_goals try omega

theorem zagierMap_branchTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) (hleft : t.y.val - t.z.val < t.x.val)
    (hright : t.x.val < 2 * t.y.val) :
    zagierMapOfPrimeNeTwo hp hp2 (branchTwo t hleft hright) = t := by
  have h1raw : ¬ 2 * t.y.val - t.x.val < t.y.val - (t.x.val + t.z.val - t.y.val) := by
    omega
  have h2raw : 2 * t.y.val - t.x.val < 2 * t.y.val := by
    have hx := t.x_pos
    omega
  ext
  all_goals simp [zagierMapOfPrimeNeTwo, branchTwo, h1raw, h2raw]
  all_goals try omega

theorem zagierMap_branchThree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) (h : 2 * t.y.val < t.x.val) :
    zagierMapOfPrimeNeTwo hp hp2 (branchThree t h) = t := by
  have h1raw : t.x.val - 2 * t.y.val < (t.x.val - t.y.val + t.z.val) - t.y.val := by
    have hz := t.z_pos
    omega
  ext
  all_goals simp [zagierMapOfPrimeNeTwo, branchThree, branchOne, h1raw]
  all_goals try omega

theorem zagierMap_involutive {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Involutive (zagierMapOfPrimeNeTwo hp hp2) := by
  intro t
  by_cases h1 : t.x.val < t.y.val - t.z.val
  · simpa [zagierMapOfPrimeNeTwo, h1] using zagierMap_branchOne hp hp2 t h1
  · by_cases h2 : t.x.val < 2 * t.y.val
    · have hleft : t.y.val - t.z.val < t.x.val := by
        have hne := ne_y_sub_z_of_prime hp t
        omega
      simpa [zagierMapOfPrimeNeTwo, h1, h2] using zagierMap_branchTwo hp hp2 t hleft h2
    · have h3 : 2 * t.y.val < t.x.val := by
        have hne := ne_two_mul_y_of_prime_ne_two hp hp2 t
        omega
      simpa [zagierMapOfPrimeNeTwo, h1, h2] using zagierMap_branchThree hp hp2 t h3

theorem branchOne_ne_self {p : ℕ} (t : ZagierTriple p)
    (h : t.x.val < t.y.val - t.z.val) :
    branchOne t h ≠ t := by
  intro hf
  have hy := congrArg (fun s : ZagierTriple p => s.y.val) hf
  have hz := congrArg (fun s : ZagierTriple p => s.z.val) hf
  simp [branchOne] at hy hz
  omega

theorem branchThree_ne_self {p : ℕ} (t : ZagierTriple p) (h : 2 * t.y.val < t.x.val) :
    branchThree t h ≠ t := by
  intro hf
  have hx := congrArg (fun s : ZagierTriple p => s.x.val) hf
  have hy := t.y_pos
  simp [branchThree] at hx
  omega

theorem branchTwo_fixed_x_eq_y {p : ℕ} (t : ZagierTriple p)
    (hleft : t.y.val - t.z.val < t.x.val) (hright : t.x.val < 2 * t.y.val)
    (hf : branchTwo t hleft hright = t) : t.x.val = t.y.val := by
  have hx := congrArg (fun s : ZagierTriple p => s.x.val) hf
  simp [branchTwo] at hx
  omega

theorem zagierMap_fixed_x_eq_y {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) (hfix : zagierMapOfPrimeNeTwo hp hp2 t = t) :
    t.x.val = t.y.val := by
  by_cases h1 : t.x.val < t.y.val - t.z.val
  · have hf : branchOne t h1 = t := by
      simpa [zagierMapOfPrimeNeTwo, h1] using hfix
    exact False.elim (branchOne_ne_self t h1 hf)
  · by_cases h2 : t.x.val < 2 * t.y.val
    · have hleft : t.y.val - t.z.val < t.x.val := by
        have hne := ne_y_sub_z_of_prime hp t
        omega
      have hf : branchTwo t hleft h2 = t := by
        simpa [zagierMapOfPrimeNeTwo, h1, h2] using hfix
      exact branchTwo_fixed_x_eq_y t hleft h2 hf
    · have h3 : 2 * t.y.val < t.x.val := by
        have hne := ne_two_mul_y_of_prime_ne_two hp hp2 t
        omega
      have hf : branchThree t h3 = t := by
        simpa [zagierMapOfPrimeNeTwo, h1, h2] using hfix
      exact False.elim (branchThree_ne_self t h3 hf)

theorem x_eq_one_of_prime_and_x_eq_y {p : ℕ} (hp : p.Prime) (t : ZagierTriple p)
    (hxy : t.x.val = t.y.val) : t.x.val = 1 := by
  by_contra hne
  have hp_eq : p = t.x.val * (t.x.val + 4 * t.z.val) := by
    calc
      p = t.x.val ^ 2 + 4 * t.y.val * t.z.val := t.equation.symm
      _ = t.x.val * (t.x.val + 4 * t.z.val) := by
        rw [← hxy]
        ring
  have hdiv : t.x.val ∣ p := ⟨t.x.val + 4 * t.z.val, hp_eq⟩
  have hpx : p = t.x.val := (hp.dvd_iff_eq hne).mp hdiv
  have hx := t.x_pos
  have hz := t.z_pos
  nlinarith

theorem zagierMap_fixed_xy_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) (hfix : zagierMapOfPrimeNeTwo hp hp2 t = t) :
    t.x.val = 1 ∧ t.y.val = 1 := by
  have hxy := zagierMap_fixed_x_eq_y hp hp2 t hfix
  have hx1 := x_eq_one_of_prime_and_x_eq_y hp t hxy
  constructor
  · exact hx1
  · omega

theorem zagierMap_fixed_unique {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a b : ZagierTriple p}
    (ha : zagierMapOfPrimeNeTwo hp hp2 a = a)
    (hb : zagierMapOfPrimeNeTwo hp hp2 b = b) : a = b := by
  have haxy := zagierMap_fixed_xy_one hp hp2 a ha
  have hbxy := zagierMap_fixed_xy_one hp hp2 b hb
  ext
  · exact haxy.1.trans hbxy.1.symm
  · exact haxy.2.trans hbxy.2.symm
  · have haeq := a.equation
    have hbeq := b.equation
    rw [haxy.1, haxy.2] at haeq
    rw [hbxy.1, hbxy.2] at hbeq
    omega

theorem zagierMap_canonicalTriple_fixed (k : ℕ) (hk : 0 < k)
    (hp : (4 * k + 1).Prime) :
    zagierMapOfPrimeNeTwo hp (by omega : 4 * k + 1 ≠ 2) (canonicalTriple k hk) =
      canonicalTriple k hk := by
  have h1 : ¬ (1 : ℕ) < 1 - k := by omega
  have h2 : (1 : ℕ) < 2 * 1 := by omega
  ext
  all_goals simp [zagierMapOfPrimeNeTwo, canonicalTriple, branchTwo, h1, h2]

theorem existsUnique_zagierMap_fixed_of_four_mul_add_one (k : ℕ) (hk : 0 < k)
    (hp : (4 * k + 1).Prime) :
    ∃! t : ZagierTriple (4 * k + 1),
      zagierMapOfPrimeNeTwo hp (by omega : 4 * k + 1 ≠ 2) t = t := by
  let hp2 : 4 * k + 1 ≠ 2 := by omega
  refine ⟨canonicalTriple k hk, ?_, ?_⟩
  · exact zagierMap_canonicalTriple_fixed k hk hp
  · intro t ht
    exact zagierMap_fixed_unique hp hp2 ht (zagierMap_canonicalTriple_fixed k hk hp)

theorem card_odd_of_four_mul_add_one (k : ℕ) (hk : 0 < k)
    (hp : (4 * k + 1).Prime) : Odd (Fintype.card (ZagierTriple (4 * k + 1))) := by
  classical
  let hp2 : 4 * k + 1 ≠ 2 := by omega
  exact odd_card_of_involutive_unique_fixed
    (zagierMapOfPrimeNeTwo hp hp2)
    (zagierMap_involutive hp hp2)
    (existsUnique_zagierMap_fixed_of_four_mul_add_one k hk hp)









theorem swapYZ_fixed_iff (p : ℕ) (t : ZagierTriple p) : (swapYZ p) t = t ↔ t.y = t.z := by
  constructor
  · intro h
    have := congrArg ZagierTriple.y h
    simpa using this.symm
  · intro hyz
    cases t
    simp at hyz
    subst hyz
    rfl

theorem exists_sq_add_sq_of_y_eq_z {p : ℕ} (t : ZagierTriple p) (hyz : t.y = t.z) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  refine ⟨t.x.val, 2 * t.y.val, ?_⟩
  have heq := t.equation
  rw [← hyz] at heq
  nlinarith

theorem exists_sq_add_sq_of_swapYZ_fixed {p : ℕ} (t : ZagierTriple p) (hfix : (swapYZ p) t = t) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  exists_sq_add_sq_of_y_eq_z t ((swapYZ_fixed_iff p t).mp hfix)

theorem exists_swapYZ_fixed_of_odd_card {p : ℕ} (hodd : Odd (Fintype.card (ZagierTriple p))) :
    ∃ t : ZagierTriple p, (swapYZ p) t = t := by
  have hinv : (swapYZ p : Equiv.Perm (ZagierTriple p)) ^ 2 = 1 := by
    apply Equiv.ext
    intro t
    cases t
    rfl
  exact exists_fixed_of_odd_card_involutive (swapYZ p) hodd hinv

theorem exists_sq_add_sq_of_four_mul_add_one_prime (k : ℕ) (hk : 0 < k)
    (hp : (4 * k + 1).Prime) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  have hodd := card_odd_of_four_mul_add_one k hk hp
  rcases exists_swapYZ_fixed_of_odd_card hodd with ⟨t, hfix⟩
  exact exists_sq_add_sq_of_swapYZ_fixed t hfix



end ZagierTriple



/-!
### Full characterization

A positive integer n is a sum of two squares iff every prime q ≡ 3 (mod 4)
dividing n appears to an even power.
-/





end ProofsInTheBook.Chapter04

open Nat
open ProofsInTheBook.Chapter04
open ProofsInTheBook.Chapter04.ZagierTriple

theorem solution (p : ℕ) (hp : p.Prime)
    (hmod : p % 4 = 1) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  let k := p / 4
  have hp_eq : p = 4 * k + 1 := by
    omega
  have hk : 0 < k := by
    have hpgt : 1 < p := hp.one_lt
    omega
  have hkprime : (4 * k + 1).Prime := by
    rwa [← hp_eq]
  rcases exists_sq_add_sq_of_four_mul_add_one_prime k hk hkprime with ⟨a, b, h⟩
  refine ⟨a, b, ?_⟩
  rwa [hp_eq]
