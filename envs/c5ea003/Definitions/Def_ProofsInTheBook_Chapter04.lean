-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter04
-- name    : ProofsInTheBook_Chapter04
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T14:25:25.282686+00:00
-- url     : https://prove2.me/theorems/04c3f4f4-1f8b-4a8d-a121-989c50f7284b
-- title:
--   Chapter 4: finite triples for Zagier's involution
-- statement:
--   For a natural number $p$, define the finite set of positive triples
--   $$S_p=\{(x,y,z):0<x,y,z\le p,\ x^2+4yz=p\}.$$
--   The bundle gives this set a finite type, constructs the canonical triple $(1,1,k)$ when $p=4k+1$ with $k>0$, and defines the three branches of Zagier's map. For prime $p\ne2$, the branches combine into a map from $S_p$ to itself. It also defines the map $(x,y,z)\mapsto(x,z,y)$.
--
--   The supporting arithmetic proofs establish that these constructions preserve positivity and the defining equation. The involution and fixed-point arguments used to prove the two-squares theorem are in the separate theorem solution.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, sixth edition (2018), Chapter 4, Representing numbers as sums of two squares; https://doi.org/10.1007/978-3-662-57265-8. Exact Lean source: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter04.lean#L103-L507

import Mathlib

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

/-- Finite ambient version of Zagier's triples `x^2 + 4yz = p`. -/
structure ZagierTriple (p : ℕ) where
  x : Fin (p + 1)
  y : Fin (p + 1)
  z : Fin (p + 1)
  x_pos : 0 < x.val
  y_pos : 0 < y.val
  z_pos : 0 < z.val
  equation : x.val ^ 2 + 4 * y.val * z.val = p

namespace ZagierTriple



instance instFintype (p : ℕ) : Fintype (ZagierTriple p) := by
  classical
  let S : Type := {u : Fin (p + 1) × Fin (p + 1) × Fin (p + 1) //
    0 < u.1.val ∧ 0 < u.2.1.val ∧ 0 < u.2.2.val ∧
      u.1.val ^ 2 + 4 * u.2.1.val * u.2.2.val = p}
  let e : ZagierTriple p ≃ S :=
    { toFun := fun t => ⟨(t.x, t.y, t.z), by
        exact ⟨t.x_pos, t.y_pos, t.z_pos, t.equation⟩⟩
      invFun := fun u =>
        { x := u.1.1
          y := u.1.2.1
          z := u.1.2.2
          x_pos := u.2.1
          y_pos := u.2.2.1
          z_pos := u.2.2.2.1
          equation := u.2.2.2.2 }
      left_inv := by
        intro t
        cases t
        rfl
      right_inv := by
        intro u
        rcases u with ⟨⟨x, y, z⟩, hx, hy, hz, heq⟩
        rfl }
  exact Fintype.ofEquiv S e.symm

def canonicalTriple (k : ℕ) (hk : 0 < k) : ZagierTriple (4 * k + 1) where
  x := ⟨1, by omega⟩
  y := ⟨1, by omega⟩
  z := ⟨k, by omega⟩
  x_pos := Nat.zero_lt_one
  y_pos := Nat.zero_lt_one
  z_pos := hk
  equation := by ring





 theorem branch_one_equation (x y z : ℕ) (h : x + z ≤ y) :
    (x + 2 * z) ^ 2 + 4 * z * (y - x - z) = x ^ 2 + 4 * y * z := by
  have hcast : ((y - x - z : ℕ) : ℤ) = (y : ℤ) - x - z := by omega
  norm_num [pow_two]
  nlinarith

def branchOne {p : ℕ} (t : ZagierTriple p) (h : t.x.val < t.y.val - t.z.val) :
    ZagierTriple p where
  x := ⟨t.x.val + 2 * t.z.val, by
    have heq := t.equation
    have hx := t.x_pos
    have hy := t.y_pos
    have hz := t.z_pos
    have hzle : 2 * t.z.val ≤ 4 * t.y.val * t.z.val := by nlinarith
    have hxle : t.x.val ≤ t.x.val ^ 2 := by nlinarith
    omega⟩
  y := t.z
  z := ⟨t.y.val - t.x.val - t.z.val, by
    exact lt_of_le_of_lt (le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)) t.y.2⟩
  x_pos := Nat.add_pos_left t.x_pos _
  y_pos := t.z_pos
  z_pos := by
    change 0 < t.y.val - t.x.val - t.z.val
    have hcomm : t.y.val - t.x.val - t.z.val = t.y.val - t.z.val - t.x.val := by omega
    rw [hcomm]
    exact Nat.sub_pos_of_lt h
  equation := by
    have hsum : t.x.val + t.z.val ≤ t.y.val := by omega
    calc
      (t.x.val + 2 * t.z.val) ^ 2 + 4 * t.z.val * (t.y.val - t.x.val - t.z.val)
          = t.x.val ^ 2 + 4 * t.y.val * t.z.val := branch_one_equation _ _ _ hsum
      _ = p := t.equation

 theorem branch_two_equation (x y z : ℕ) (hxy : x ≤ 2 * y) (hyxz : y ≤ x + z) :
    (2 * y - x) ^ 2 + 4 * y * (x + z - y) = x ^ 2 + 4 * y * z := by
  have hcast1 : ((2 * y - x : ℕ) : ℤ) = 2 * (y : ℤ) - x := by omega
  have hcast2 : ((x + z - y : ℕ) : ℤ) = (x : ℤ) + z - y := by omega
  norm_num [pow_two]
  nlinarith

def branchTwo {p : ℕ} (t : ZagierTriple p)
    (hleft : t.y.val - t.z.val < t.x.val) (hright : t.x.val < 2 * t.y.val) :
    ZagierTriple p where
  x := ⟨2 * t.y.val - t.x.val, by
    have heq := t.equation
    have hy := t.y_pos
    have hz := t.z_pos
    have hyle : 2 * t.y.val ≤ 4 * t.y.val * t.z.val := by nlinarith
    omega⟩
  y := t.y
  z := ⟨t.x.val + t.z.val - t.y.val, by
    have heq := t.equation
    have hx := t.x_pos
    have hy := t.y_pos
    have hz := t.z_pos
    have hzle : t.z.val ≤ 4 * t.y.val * t.z.val := by nlinarith
    have hxle : t.x.val ≤ t.x.val ^ 2 := by nlinarith
    omega⟩
  x_pos := by
    change 0 < 2 * t.y.val - t.x.val
    exact Nat.sub_pos_of_lt hright
  y_pos := t.y_pos
  z_pos := by
    change 0 < t.x.val + t.z.val - t.y.val
    have hyxz : t.y.val < t.x.val + t.z.val := by omega
    exact Nat.sub_pos_of_lt hyxz
  equation := by
    have hxy : t.x.val ≤ 2 * t.y.val := by omega
    have hyxz : t.y.val ≤ t.x.val + t.z.val := by omega
    calc
      (2 * t.y.val - t.x.val) ^ 2 + 4 * t.y.val * (t.x.val + t.z.val - t.y.val)
          = t.x.val ^ 2 + 4 * t.y.val * t.z.val := branch_two_equation _ _ _ hxy hyxz
      _ = p := t.equation

 theorem branch_three_equation (x y z : ℕ) (h2y : 2 * y ≤ x) :
    (x - 2 * y) ^ 2 + 4 * (x - y + z) * y = x ^ 2 + 4 * y * z := by
  apply Int.ofNat.inj
  norm_num [pow_two]
  have hyx : y ≤ x := by omega
  have hcast1 : ((x - 2 * y : ℕ) : ℤ) = (x : ℤ) - 2 * y := by omega
  have hcast2 : ((x - y : ℕ) : ℤ) = (x : ℤ) - y := by omega
  rw [hcast1, hcast2]
  ring

def branchThree {p : ℕ} (t : ZagierTriple p) (h : 2 * t.y.val < t.x.val) :
    ZagierTriple p where
  x := ⟨t.x.val - 2 * t.y.val, by
    exact lt_of_le_of_lt (Nat.sub_le _ _) t.x.2⟩
  y := ⟨t.x.val - t.y.val + t.z.val, by
    have heq := t.equation
    have hx := t.x_pos
    have hy := t.y_pos
    have hz := t.z_pos
    have hzle : t.z.val ≤ 4 * t.y.val * t.z.val := by nlinarith
    have hxle : t.x.val ≤ t.x.val ^ 2 := by nlinarith
    omega⟩
  z := t.y
  x_pos := by
    change 0 < t.x.val - 2 * t.y.val
    exact Nat.sub_pos_of_lt h
  y_pos := by
    change 0 < t.x.val - t.y.val + t.z.val
    have hyx : t.y.val < t.x.val := by omega
    exact Nat.add_pos_left (Nat.sub_pos_of_lt hyx) _
  z_pos := t.y_pos
  equation := by
    have h2y : 2 * t.y.val ≤ t.x.val := by omega
    calc
      (t.x.val - 2 * t.y.val) ^ 2 + 4 * (t.x.val - t.y.val + t.z.val) * t.y.val
          = t.x.val ^ 2 + 4 * t.y.val * t.z.val := branch_three_equation _ _ _ h2y
      _ = p := t.equation

theorem ne_y_sub_z_of_prime {p : ℕ} (hp : p.Prime) (t : ZagierTriple p) :
    t.x.val ≠ t.y.val - t.z.val := by
  intro h
  have hx := t.x_pos
  have hsum : t.y.val = t.x.val + t.z.val := by omega
  have heq : (t.x.val + 2 * t.z.val) ^ 2 = p := by
    calc
      (t.x.val + 2 * t.z.val) ^ 2 = t.x.val ^ 2 + 4 * t.y.val * t.z.val := by
        rw [hsum]
        ring
      _ = p := t.equation
  have hprimepow : ((t.x.val + 2 * t.z.val) ^ 2).Prime := by
    simpa [heq] using hp
  exact Nat.Prime.not_prime_pow (x := t.x.val + 2 * t.z.val) (n := 2) (by norm_num) hprimepow

theorem ne_two_mul_y_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) :
    t.x.val ≠ 2 * t.y.val := by
  intro h
  have hpeven : Even p := by
    refine even_iff_two_dvd.mpr ?_
    rw [← t.equation]
    rw [h]
    ring_nf
    omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  exact hpodd.not_two_dvd_nat (even_iff_two_dvd.mp hpeven)

def zagierMapOfPrimeNeTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ZagierTriple p → ZagierTriple p := fun t => by
  by_cases h1 : t.x.val < t.y.val - t.z.val
  · exact branchOne t h1
  · by_cases h2 : t.x.val < 2 * t.y.val
    · exact branchTwo t (by
        have hne := ne_y_sub_z_of_prime hp t
        omega) h2
    · exact branchThree t (by
        have hne := ne_two_mul_y_of_prime_ne_two hp hp2 t
        omega)





























/-- The simple involution `(x,y,z) ↦ (x,z,y)` on Zagier triples. -/
def swapYZ (p : ℕ) : ZagierTriple p ≃ ZagierTriple p where
  toFun t :=
    { x := t.x
      y := t.z
      z := t.y
      x_pos := t.x_pos
      y_pos := t.z_pos
      z_pos := t.y_pos
      equation := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using t.equation }
  invFun t :=
    { x := t.x
      y := t.z
      z := t.y
      x_pos := t.x_pos
      y_pos := t.z_pos
      z_pos := t.y_pos
      equation := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using t.equation }
  left_inv t := by
    cases t
    rfl
  right_inv t := by
    cases t
    rfl



















end ZagierTriple



/-!
### Full characterization

A positive integer n is a sum of two squares iff every prime q ≡ 3 (mod 4)
dividing n appears to an even power.
-/





end ProofsInTheBook.Chapter04


