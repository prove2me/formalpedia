-- Prove2me | Theorems.Thm_WilliamsonShmoys_list_partition_into_at_least_three
-- name    : WilliamsonShmoys.list_partition_into_at_least_three
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T02:43:12.358516+00:00
-- url     : https://prove2.me/theorems/e3790e8a-c2fc-49d4-8da1-4befcc575012
-- title:
--   Distribute a list into sufficiently large lists
-- statement:
--   A list with at least 3k entries can be split into exactly k lists, preserving its entries and total length, with every resulting entry drawn from the original list. This child supplies the list-count and length facts needed to build the certificate. A constructive proof divides the list into blocks of three and leaves the remainder in the final block; the k=0 case follows because the capacity assumption forces an empty input.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.list_partition_into_at_least_three
    {α : Type} (xs : List α) (k : Nat)
    (hcapacity : 3 * k ≤ xs.length) :
    ∃ fs : List (List α),
      fs.length = k ∧
      List.Perm fs.flatten xs ∧
      (∀ face ∈ fs, ∀ x ∈ face, x ∈ xs) ∧
      3 * k ≤ (fs.map List.length).sum ∧
      (fs.map List.length).sum = xs.length := by sorry
