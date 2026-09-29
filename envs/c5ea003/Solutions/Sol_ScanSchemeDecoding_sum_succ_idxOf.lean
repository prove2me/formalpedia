-- Prove2me | solution 1 for ScanSchemeDecoding.sum_succ_idxOf
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:00:09.509368+00:00
-- url     : https://prove2.me/submissions/4b367023-f4ce-4f98-b1c1-c8b6c1a3989e

-- Sol generated from Algebra/ScanSchemeDecoding/Core.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_triangle_succ

/-!
# Scan schemes: honest uniqueness decoding and exact cost accounting

A **scan scheme** on a finite key type `α` with bucket labels in `β` is nothing but a
bucket map `bucket : α → β`.  Decoding a key means scanning its bucket, in the
canonical (linear) order, until the key is found.  Two things are then formalised
here, and both are *exact*, not asymptotic:

* **Honest uniqueness decoding** (`ScanScheme.honest_scanCode`,
  `ScanScheme.decode_eq_some_iff`).  The pair `encode x = (bucket x, idx x)`
  — bucket label together with the *intra-bucket index* — decodes back to `x`, and
  it is the **only** pair that does so.  So `encode` is an injection into
  `β × ℕ` whose decoding is unambiguous: no scheme-level ambiguity is hidden in the
  cost model.
* **Exact cost accounting** (`ScanScheme.decodeCost_eq`).  The total decoding cost
  `∑ x, decodeCost x` equals `∑ b, triangle (fiber b).card` *on the nose*.

The two facts together turn the optimisation of scan schemes into the purely
arithmetic problem solved in `Algebra.ScanSchemeDecoding.Triangle`.
-/

open ScanSchemeDecoding

open Finset


variable {α β : Type*} [Fintype α] [LinearOrder α] [DecidableEq β]

open ScanScheme

variable (S : ScanScheme α β)





















open ScanScheme

variable (S : ScanScheme α β)






open ScanSchemeDecoding in
theorem solution{γ : Type*} [DecidableEq γ] :
    ∀ (l : List γ), l.Nodup → ∑ x ∈ l.toFinset, (l.idxOf x + 1) = triangle l.length := by
  intro l
  induction l with
  | nil => simp [triangle]
  | cons a t ih =>
    intro hnd
    have ha : a ∉ t := (List.nodup_cons.mp hnd).1
    have hndt : t.Nodup := (List.nodup_cons.mp hnd).2
    have ha' : a ∉ t.toFinset := by simpa using ha
    rw [List.toFinset_cons, Finset.sum_insert ha']
    have h0 : (a :: t).idxOf a + 1 = 1 := by simp
    have hstep : ∀ x ∈ t.toFinset, (a :: t).idxOf x + 1 = (t.idxOf x + 1) + 1 := by
      intro x hx
      have hxa : a ≠ x := by
        intro h; exact ha (by simpa [h] using List.mem_toFinset.mp hx)
      rw [List.idxOf_cons_ne _ hxa]
    rw [h0, Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ih hndt]
    have hcard : t.toFinset.card = t.length := List.toFinset_card_of_nodup hndt
    simp only [Finset.sum_const, hcard, smul_eq_mul, mul_one]
    rw [List.length_cons, triangle_succ]
    omega
