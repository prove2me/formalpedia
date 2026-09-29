-- Prove2me | solution 1 for ScanSchemeDecoding.ScanScheme.encode_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:01:39.959367+00:00
-- url     : https://prove2.me/submissions/5fd52962-f406-45f8-8d0d-994c602f1767

-- Sol generated from Algebra/ScanSchemeDecoding/Core.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_mem_scanList

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












lemma self_mem_scanList (x : α) : x ∈ S.scanList (S.bucket x) := by simp

/-- **Honest uniqueness decoding.**  The scan code of a key decodes back to that key. -/
theorem honest_scanCode (x : α) : S.decode (S.encode x) = some x := by
  classical
  exact List.getElem?_idxOf (l := S.scanList (S.bucket x)) (a := x) (self_mem_scanList S x)








open ScanScheme

variable (S : ScanScheme α β)






open ScanSchemeDecoding in
theorem solution: Function.Injective S.encode := by
  intro x y h
  have hx := honest_scanCode S x
  rw [h, honest_scanCode S y] at hx
  exact (Option.some.inj hx).symm
