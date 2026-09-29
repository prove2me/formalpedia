-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
-- name    : Algebra_TropicalLinearAlgebra_TropicalEigenvalue
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:24:49.1595+00:00
-- url     : https://prove2.me/theorems/7fecd97f-5ccd-4916-9a1c-59f2e3978fd2
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_TropicalEigenvalue
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.TropicalEigenvalue`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
/-
# Tropical eigenvalues and the max-plus Perron–Frobenius theorem

An eigenpair of a max-plus matrix `A` (finite real entries) is a pair `(lam, v)`
with `A ⊗ v = lam ⊗ v`, i.e.

  `max_j (A i j + v j) = lam + v i`  for every `i`.

Main results of this file:

* `IsTropEigen.cycle_le` : every closed walk (cycle) of `A` has weight at most
  `length · lam` — an eigenvalue dominates all cycle means;
* `IsTropEigen.exists_critical_cycle` : some *simple* cycle attains the mean `lam`
  exactly (the critical cycle), obtained from the argmax function of the eigenvector
  by a minimal-period pigeonhole argument;
* `IsTropEigen.isGreatest_cycleMean` : **tropical Perron–Frobenius (spectral part)** —
  `lam` is the *maximum cycle mean* of `A`, and hence
* `tropEigenvalue_unique` : a max-plus matrix has at most one eigenvalue.
-/

namespace TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- `lam` is a **tropical eigenvalue** of `A` with eigenvector `v` (all entries finite)
if `A ⊗ v = lam ⊗ v`. -/
def IsTropEigen (A : Matrix ι ι ℝ) (lam : ℝ) (v : ι → ℝ) : Prop :=
  ∀ i, tmulVec A v i = lam + v i


theorem exists_tmulVec_eq (A : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) :
    ∃ j, tmulVec A v i = A i j + v j := by
  obtain ⟨j, _, hj⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) (fun j => A i j + v j)
  exact ⟨j, hj⟩

namespace IsTropEigen

variable {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}





theorem exists_tight (h : IsTropEigen A lam v) (i : ι) : ∃ j, A i j + v j = lam + v i := by
  obtain ⟨j, hj⟩ := exists_tmulVec_eq A v i
  exact ⟨j, by rw [← hj, h i]⟩

section CriticalCycle

/-- A choice of tight successor for each index, together with a point of **minimal**
period for that choice function.  This is the combinatorial heart of tropical
Perron–Frobenius: following the argmax of the eigenvector must eventually cycle. -/
theorem exists_minimal_periodic_point (h : IsTropEigen A lam v) :
    ∃ (f : ι → ι) (y : ι) (p : ℕ), 0 < p ∧ f^[p] y = y ∧
      (∀ q, 0 < q → q < p → f^[q] y ≠ y) ∧ (∀ i, A i (f i) + v (f i) = lam + v i) := by
  classical
  choose f hf using h.exists_tight
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] i₀)
  -- normalise so that `a < b`
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact aux f hf i₀ a b hlt hfab
  · exact aux f hf i₀ b a hlt hfab.symm
where
  aux (f : ι → ι) (hf : ∀ i, A i (f i) + v (f i) = lam + v i) (i₀ : ι) (a b : ℕ) (hlt : a < b)
      (hfab : f^[a] i₀ = f^[b] i₀) :
      ∃ (f : ι → ι) (y : ι) (p : ℕ), 0 < p ∧ f^[p] y = y ∧
        (∀ q, 0 < q → q < p → f^[q] y ≠ y) ∧ (∀ i, A i (f i) + v (f i) = lam + v i) := by
    classical
    set y₀ := f^[a] i₀ with hy₀
    have hper : f^[b - a] y₀ = y₀ := by
      rw [hy₀, ← Function.iterate_add_apply f (b - a) a i₀]
      have : b - a + a = b := by omega
      rw [this, ← hfab]
    have hex : ∃ q, 0 < q ∧ f^[q] y₀ = y₀ := ⟨b - a, by omega, hper⟩
    classical
    let p := Nat.find hex
    have hp := Nat.find_spec hex
    refine ⟨f, y₀, p, hp.1, hp.2, ?_, hf⟩
    intro q hq hqp hcontra
    have hmem : 0 < q ∧ f^[q] y₀ = y₀ := ⟨hq, hcontra⟩
    have hle : p ≤ q := Nat.find_le hmem
    omega



end CriticalCycle


end IsTropEigen


end TropicalLA


