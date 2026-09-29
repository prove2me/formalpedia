-- Prove2me | solution 1 for ScanSchemeDecoding.sum_triangle_eq_opt_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:55:48.669393+00:00
-- url     : https://prove2.me/submissions/89ca23d0-cf68-4a42-96e7-62a8dd337c93

-- Sol generated from Algebra/ScanSchemeDecoding/Rigidity.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_sum_tangent_eq
import Theorems.Thm_ScanSchemeDecoding_triangleOpt_eq
import Theorems.Thm_ScanSchemeDecoding_triangle_succ
import Theorems.Thm_ScanSchemeDecoding_triangle_tangent
import Theorems.Thm_ScanSchemeDecoding_two_mul_triangle

/-!
# Rigidity of the optimum, collision-freeness, and symmetry of the cost

The lower bound of `Algebra.ScanSchemeDecoding.Optimum` is not only sharp, it is
*rigid*: the tangent-line argument leaves a slack `(d)(d-1)/2` in each bucket, where
`d` is the deviation of the bucket size from `⌊N/m⌋`.  Since `d(d-1) = 0` only for
`d ∈ {0, 1}`, the optimum is attained **exactly** by the balanced size profiles.

## Main results

* `ScanSchemeDecoding.sum_triangle_eq_opt_iff` — rigidity at the level of size profiles.
* `ScanSchemeDecoding.ScanScheme.decodeCost_eq_opt_iff` — a scan scheme is cost-optimal
  iff every bucket has size `⌊N/m⌋` or `⌈N/m⌉`.
* `ScanSchemeDecoding.ScanScheme.decodeCost_eq_one_iff` — unit decoding cost everywhere
  is *equivalent* to injectivity of the bucket map (perfect hashing).
* `ScanSchemeDecoding.ScanScheme.exists_two_le_decodeCost` — fewer buckets than keys
  forces a key of cost `≥ 2`.
* `ScanSchemeDecoding.ScanScheme.decodeCost_perm_invariant`,
  `ScanSchemeDecoding.ScanScheme.decodeCost_relabel` — the total cost is invariant under
  the natural `Sym(α) × Sym(β)`-action, i.e. it is a function of the bucket-size
  partition alone.
-/

open ScanSchemeDecoding

open Finset


open ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)








open ScanSchemeDecoding in
theorem solution{m : ℕ} (hm : 0 < m) (f : Fin m → ℕ) (N : ℕ)
    (hf : ∑ i, f i = N) :
    ∑ i, triangle (f i) = triangleOpt N m ↔ ∀ i, N / m ≤ f i ∧ f i ≤ N / m + 1 := by
  classical
  constructor
  · intro hopt i
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ (triangle (f j) : ℤ)
          - ((triangle (N / m) : ℤ) + (((N / m : ℕ) : ℤ) + 1) * ((f j : ℤ) - ((N / m : ℕ) : ℤ))) :=
      fun j _ => by linarith [triangle_tangent (N / m) (f j)]
    have hsum0 : ∑ j : Fin m, ((triangle (f j) : ℤ)
        - ((triangle (N / m) : ℤ)
          + (((N / m : ℕ) : ℤ) + 1) * ((f j : ℤ) - ((N / m : ℕ) : ℤ)))) = 0 := by
      rw [Finset.sum_sub_distrib, sum_tangent_eq hm f N hf, ← Nat.cast_sum, hopt]
      ring
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 i (Finset.mem_univ i)
    have h2k : (2 : ℤ) * triangle (f i) = (f i : ℤ) * ((f i : ℤ) + 1) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (two_mul_triangle (f i))
    have h2q : (2 : ℤ) * triangle (N / m) = ((N / m : ℕ) : ℤ) * (((N / m : ℕ) : ℤ) + 1) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (two_mul_triangle (N / m))
    have hd : ((f i : ℤ) - ((N / m : ℕ) : ℤ)) * ((f i : ℤ) - ((N / m : ℕ) : ℤ) - 1) = 0 := by
      linear_combination 2 * hzero - h2k + h2q
    rcases mul_eq_zero.mp hd with h | h
    · have hcast : (f i : ℤ) = ((N / m : ℕ) : ℤ) := by linarith
      have hnat : f i = N / m := by exact_mod_cast hcast
      exact ⟨hnat.ge, by rw [hnat]; exact Nat.le_succ _⟩
    · have hcast : (f i : ℤ) = ((N / m : ℕ) : ℤ) + 1 := by linarith
      have hnat : f i = N / m + 1 := by exact_mod_cast hcast
      exact ⟨by rw [hnat]; exact Nat.le_succ _, hnat.le⟩
  · intro hb
    have hcast : ∀ i : Fin m,
        triangle (f i) = triangle (N / m) + (f i - N / m) * (N / m + 1) := by
      intro i
      rcases Nat.eq_or_lt_of_le (hb i).1 with h | h
      · rw [← h]
        simp
      · have hub := (hb i).2
        have hfi : f i = N / m + 1 := by omega
        rw [hfi, triangle_succ]
        simp
    have hsplit : ∑ i : Fin m, f i = ∑ i : Fin m, (N / m + (f i - N / m)) :=
      Finset.sum_congr rfl (fun i _ => (Nat.add_sub_cancel' (hb i).1).symm)
    rw [Finset.sum_add_distrib] at hsplit
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsplit
    have hsumc : ∑ i : Fin m, (f i - N / m) = N % m := by
      have h1 : m * (N / m) + ∑ i : Fin m, (f i - N / m) = m * (N / m) + N % m := by
        rw [← hsplit, hf]
        exact (Nat.div_add_mod N m).symm
      exact Nat.add_left_cancel h1
    rw [Finset.sum_congr rfl (fun i _ => hcast i), Finset.sum_add_distrib, ← Finset.sum_mul,
      hsumc, triangleOpt_eq hm]
    simp
