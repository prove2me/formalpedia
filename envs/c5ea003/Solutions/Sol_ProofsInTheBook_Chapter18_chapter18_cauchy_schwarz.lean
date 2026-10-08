-- Prove2me | solution 1 for ProofsInTheBook.Chapter18.chapter18_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T15:18:20.093233+00:00
-- url     : https://prove2.me/submissions/90636646-35e9-4eb4-9a2f-fdfed8eb05a7

import Mathlib


/-!
# Chapter 18: In praise of inequalities

From "Proofs from THE BOOK":

**AM-GM inequality**: the geometric mean of finitely many non-negative reals is at most
their arithmetic mean.  The two-variable case `√(ab) ≤ (a+b)/2` is the book's warm-up
(from `(√a - √b)² ≥ 0`); the headline `chapter18` is the general `n`-variable statement.

**Cauchy-Schwarz**: `(∑ aᵢbᵢ)² ≤ (∑ aᵢ²)(∑ bᵢ²)`, the discriminant inequality.
-/

namespace ProofsInTheBook.Chapter18

/-!
### AM-GM: the (a-b)² ≥ 0 trick (two-variable warm-up)
-/







/-!
### General AM-GM and Cauchy-Schwarz
-/





end ProofsInTheBook.Chapter18

open ProofsInTheBook.Chapter18

theorem solution {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq s f g
