-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter38
-- name    : ProofsInTheBook_Chapter38
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T15:57:20.421069+00:00
-- url     : https://prove2.me/theorems/16ac2b1d-7b73-4ace-8e1e-278e59a9ac51
-- title:
--   Finite q-ary words and Hamming balls
-- statement:
--   For natural numbers $q,n$, a $q$-ary word of length $n$ is a function $\operatorname{Fin}(n)\to\operatorname{Fin}(q)$. For a word $x$ and a natural radius $r$, its Hamming ball is
--   $$B_r(x)=\{y:\operatorname{Fin}(n)\to\operatorname{Fin}(q):d_H(x,y)\le r\},$$
--   where $d_H$ counts coordinates at which the two words differ. For $q>0$, the zero word has every coordinate equal to $0$, and the ball-volume function is $V_q(n,r)=|B_r(0)|$. For $q=0$, this volume function is explicitly defined to be $0$.
--
--   Given words $x,y$, a coordinatewise transposition swaps the symbols $x_i$ and $y_i$ at each coordinate and leaves all other symbols fixed. The bundle includes the induced correspondence between equal-radius balls centered at $x$ and $y$. The volume is a finite cardinality, not a separately defined binomial-sum expression.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 42, “Communicating without errors”, pp. 291–300 (https://doi.org/10.1007/978-3-662-57265-8_42). Original definition source: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter38.lean#L31. The generated bundle retains definitions and supporting declarations from this source; the book citation identifies their topic rather than asserting that each auxiliary structure appears in the book.

import Mathlib

/-!
# Chapter 38: Communicating without errors

From "Proofs from THE BOOK":

**Intended chapter content.** The chapter discusses error-correcting codes,
including the Singleton bound, the Hamming sphere-packing bound, the
Gilbert-Varshamov greedy existence bound, and the analytic Shannon capacity
formula `C = 1 - H(p)` for the binary symmetric channel.

This file formalizes the finite combinatorial bounds.  The Shannon capacity
statement is not claimed here: it requires entropy and asymptotic channel
capacity analysis, and is recorded as an honest point-17 gap/frontier rather
than as a weakened Lean theorem.
-/

namespace ProofsInTheBook.Chapter38

open Finset

/-!
### Words, Hamming balls, and volume

For a `q`-ary alphabet we use `Fin q`.  The Hamming ball volume is formalized
as the cardinality of a ball; the usual closed form
`∑ i ≤ r, (n.choose i) * (q - 1)^i` is not needed for the three finite bounds.
-/

abbrev QaryWord (q n : ℕ) : Type :=
  Fin n → Fin q



def hammingBall (q n radius : ℕ) (center : QaryWord q n) : Finset (QaryWord q n) :=
  Finset.univ.filter fun word => hammingDist center word ≤ radius

def zeroQaryWord {q n : ℕ} (hq : 0 < q) : QaryWord q n :=
  fun _ => ⟨0, hq⟩

def qaryHammingBallVolume (q n radius : ℕ) : ℕ :=
  if hq : 0 < q then (hammingBall q n radius (zeroQaryWord (q := q) (n := n) hq)).card
  else 0

def coordinateSwap {q n : ℕ} (x y : QaryWord q n) (word : QaryWord q n) : QaryWord q n :=
  fun i => Equiv.swap (x i) (y i) (word i)

@[simp]
lemma coordinateSwap_left {q n : ℕ} (x y : QaryWord q n) :
    coordinateSwap x y x = y := by
  funext i
  simp [coordinateSwap]

@[simp]
lemma coordinateSwap_right {q n : ℕ} (x y : QaryWord q n) :
    coordinateSwap x y y = x := by
  funext i
  simp [coordinateSwap]

@[simp]
lemma coordinateSwap_involutive {q n : ℕ} (x y word : QaryWord q n) :
    coordinateSwap x y (coordinateSwap x y word) = word := by
  funext i
  simp [coordinateSwap]

lemma hammingDist_coordinateSwap {q n : ℕ} (x y a b : QaryWord q n) :
    hammingDist (coordinateSwap x y a) (coordinateSwap x y b) = hammingDist a b := by
  classical
  simpa [coordinateSwap] using
    (hammingDist_comp
      (fun i : Fin n => (Equiv.swap (x i) (y i) : Fin q → Fin q))
      (x := a) (y := b)
      (fun i => (Equiv.swap (x i) (y i)).injective))

def hammingBallEquiv {q n radius : ℕ} (x y : QaryWord q n) :
    {word : QaryWord q n // word ∈ hammingBall q n radius x} ≃
      {word : QaryWord q n // word ∈ hammingBall q n radius y} where
  toFun word :=
    ⟨coordinateSwap x y word.1, by
      have hword : hammingDist x word.1 ≤ radius := by
        have hmem := word.2
        change word.1 ∈
          (Finset.univ.filter fun word : QaryWord q n => hammingDist x word ≤ radius) at hmem
        exact (mem_filter.mp hmem).2
      have hdist :
          hammingDist y (coordinateSwap x y word.1) = hammingDist x word.1 := by
        simpa using hammingDist_coordinateSwap x y x word.1
      simpa [hammingBall, hdist] using hword⟩
  invFun word :=
    ⟨coordinateSwap x y word.1, by
      have hword : hammingDist y word.1 ≤ radius := by
        have hmem := word.2
        change word.1 ∈
          (Finset.univ.filter fun word : QaryWord q n => hammingDist y word ≤ radius) at hmem
        exact (mem_filter.mp hmem).2
      have hdist :
          hammingDist x (coordinateSwap x y word.1) = hammingDist y word.1 := by
        simpa using hammingDist_coordinateSwap x y y word.1
      simpa [hammingBall, hdist] using hword⟩
  left_inv word := by
    ext i
    simp
  right_inv word := by
    ext i
    simp





/-!
### Unique decoding

Hamming balls of radius `t` around distinct codewords are disjoint when the
minimum distance is greater than `2t`.
-/



/-!
### Singleton bound

If a `q`-ary length-`n` code has minimum distance at least `d`, then puncturing
to the first `n + 1 - d` coordinates is injective on the code.  Hence
`|C| ≤ q^(n + 1 - d)`, the natural-number rendering of `q^{n-d+1}`.
-/





/-!
### Hamming sphere-packing bound

For minimum distance at least `d` and `2t < d`, radius-`t` Hamming balls about
codewords are pairwise disjoint, so their total volume is at most the ambient
space size `q^n`.
-/



/-!
### Gilbert-Varshamov greedy existence bound

A maximum-cardinality code with minimum distance at least `d` must cover the
whole ambient space by balls of radius `d - 1`; otherwise one more word could
be inserted.  Counting that cover gives the finite Gilbert-Varshamov bound.
-/



/-!
### Chapter theorem

The finite, combinatorial Chapter 38 content proved here consists of:

* Singleton: `|C| ≤ q^(n+1-d)`.
* Hamming sphere-packing: `|C| * Vol(t) ≤ q^n` when `2t < d`.
* Gilbert-Varshamov existence: some distance-`d` code satisfies
  `q^n ≤ |C| * Vol(d-1)`.

The Shannon capacity formula remains the documented analytic frontier above.
-/



end ProofsInTheBook.Chapter38


