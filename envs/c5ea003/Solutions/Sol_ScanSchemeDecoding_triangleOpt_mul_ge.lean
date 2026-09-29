-- Prove2me | solution 1 for ScanSchemeDecoding.triangleOpt_mul_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:01:42.23633+00:00
-- url     : https://prove2.me/submissions/2cfe5acb-2729-4f53-b7e2-31c017d9901c

-- Sol generated from Algebra/ScanSchemeDecoding/Epsilon.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_triangleOpt_eq
import Theorems.Thm_ScanSchemeDecoding_two_mul_triangle

/-!
# The `ε`-compression barrier for scan indices

The exact pigeonhole optimum of `Algebra.ScanSchemeDecoding.Triangle` is stated with the
*floor* `⌊N/m⌋`.  Here we sharpen it to a statement with genuine (real) division, which
is the form in which a space/time trade-off is usually quoted:

  `N * (N + m) ≤ 2 * m * triangleOpt N m`  (`triangleOpt_mul_ge`, an exact `ℕ` statement),

and deduce the analytic corollaries

* `mean_decodeCost_ge` — the mean decoding cost of any scan scheme is at least
  `(N/m + 1)/2`;
* `mean_decodeCost_ge_inv_two_mul` — the **`ε`-compression barrier**: a scheme whose
  index uses only `m ≤ ε · N` buckets has mean decoding cost at least `1/(2ε)`.

Both are sharp: for `m ∣ N` the residue scheme of `Algebra.ScanSchemeDecoding.Optimum`
meets the first bound with equality (`mean_decodeCost_modScheme_eq` for `m ∣ N`).
-/

open ScanSchemeDecoding

open Finset







open ScanSchemeDecoding in
theorem solution{m : ℕ} (hm : 0 < m) (N : ℕ) :
    N * (N + m) ≤ 2 * m * triangleOpt N m := by
  rw [triangleOpt_eq hm]
  have hN := Nat.div_add_mod N m
  have hr : N % m < m := Nat.mod_lt _ hm
  have h2 := two_mul_triangle (N / m)
  set q := N / m with hqdef
  set r := N % m with hrdef
  set T := triangle q with hTdef
  clear_value T
  clear_value q r
  subst hN
  obtain ⟨s, hs⟩ : ∃ s, m = s + r := ⟨m - r, by omega⟩
  subst hs
  have hexp : 2 * (s + r) * ((s + r) * T + r * (q + 1))
      = (s + r) * ((s + r) * (2 * T)) + 2 * (s + r) * r * (q + 1) := by ring
  rw [hexp, h2]
  nlinarith [Nat.zero_le (r * s), Nat.zero_le q, Nat.zero_le r, Nat.zero_le s]
