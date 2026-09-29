-- Prove2me | solution 1 for KitchenQuery.tasteCost_le_cert_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:28:32.94326+00:00
-- url     : https://prove2.me/submissions/c70b5bdb-55c5-4d9f-8223-a3522050b8f9

-- Sol generated from Novelty/KitchenCertificateSquare.lean
import Mathlib
import Definitions.Def_Novelty_KitchenCertificateSquare
import Definitions.Def_Novelty_KitchenQueryComplexity
import Theorems.Thm_KitchenQuery_cert_inter_nonempty
import Theorems.Thm_KitchenQuery_exists_optimal_taste
import Theorems.Thm_KitchenQuery_queryList_eval
import Theorems.Thm_KitchenQuery_tasteCost_le_of_computes
import Theorems.Thm_KitchenQuery_tasteCost_zero_iff_constant

/-!
# `P = NP ∩ co-NP`, up to squaring, in the kitchen

Third research cycle on the query model of `Novelty.KitchenQueryComplexity`.

Cycle 1 separated deterministic from nondeterministic verification (`kitchen_P_ne_NP`) and
showed the soufflé has no nondeterministic shortcut at either verdict.  That raises the sharp
question: *if a dish has short goodness proofs and short badness proofs, must it be quick to
taste outright?*  The answer proved here is yes, up to a product:

> **Main theorem** (`tasteCost_le_cert_mul`).  If every good pantry has a goodness
> certificate of at most `m` probes and every bad pantry has a badness certificate of at most
> `k` probes, then there is a deterministic adaptive taster using at most `k * m` probes.

Equivalently `D(f) ≤ C₀(f) · C₁(f)`: in the kitchen, `NP ∩ co-NP` collapses into `P` at the
cost of squaring the tasting time.  This is exactly the boundary that the soufflé escapes:
`souffle_no_certificate_shortcut` shows both of its certificate complexities are `n`, so the
theorem only yields the vacuous bound `n²`, whereas for `anySpoiled` the bound `1 · n = n` is
attained exactly (`anySpoiled_bound_tight`).

The proof is the classical adaptive covering argument, formalised in three pieces:

* `cert_inter_nonempty`: a goodness certificate and a badness certificate always overlap —
  the combinatorial heart.
* `restrictDish`, `restrict_isCertificate`: fixing the ingredients of a certificate shrinks
  every opposite certificate by at least one probe.
* `queryList`: the tasting strategy that probes a whole checklist and then continues
  adaptively, with its depth and evaluation laws.
-/

open KitchenQuery

open Finset

variable {n : ℕ}

/-! ### Probing a whole checklist, then continuing -/


lemma queryList_depth (L : List (Fin n)) (cont : Pantry n → Taste n) {d : ℕ}
    (hcont : ∀ a, (cont a).depth ≤ d) (a : Pantry n) :
    (queryList L cont a).depth ≤ L.length + d := by
  induction L generalizing a with
  | nil => simpa [queryList] using hcont a
  | cons i L ih =>
      have h1 := ih (Function.update a i false)
      have h2 := ih (Function.update a i true)
      simp only [queryList, Taste.depth, List.length_cons]
      omega


/-! ### Certificates overlap -/


/-! ### Restricting a dish along a checklist -/


/-- Certificates of the original dish restrict to certificates of the restricted dish, with
the fixed ingredients removed. -/
theorem restrict_isCertificate {f : Dish n} {S : Finset (Fin n)} {a z : Pantry n}
    {T : Finset (Fin n)}
    (hT : IsCertificate f (fun j => if j ∈ S then a j else z j) T) :
    IsCertificate (restrictDish f S a) z (T \ S) := by
  classical
  intro y hy
  refine hT (fun j => if j ∈ S then a j else y j) ?_
  intro j hj
  by_cases hjS : j ∈ S
  · simp [hjS]
  · have : j ∈ T \ S := Finset.mem_sdiff.2 ⟨hj, hjS⟩
    simp [hjS, hy j this]

/-! ### The main theorem -/






open KitchenQuery in
theorem solution(m : ℕ) : ∀ (k : ℕ) (f : Dish n),
    (∀ x, f x = false → ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ k) →
    (∀ x, f x = true → ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ m) →
    tasteCost f ≤ k * m := by
  classical
  intro k
  induction k with
  | zero =>
      intro f h0 _
      by_cases hfalse : ∃ x, f x = false
      · obtain ⟨x0, hx0⟩ := hfalse
        obtain ⟨T, hT, hTcard⟩ := h0 x0 hx0
        have hTe : T = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hTcard)
        subst hTe
        have : ∀ y, f y = false := fun y => (hT y (by simp)).trans hx0
        simpa using ((tasteCost_zero_iff_constant f).2 ⟨false, this⟩).le
      · push_neg at hfalse
        have : ∀ y, f y = true := fun y => by
          cases hy : f y
          · exact absurd hy (hfalse y)
          · rfl
        simpa using ((tasteCost_zero_iff_constant f).2 ⟨true, this⟩).le
  | succ k ih =>
      intro f h0 h1
      by_cases htrue : ∃ x, f x = true
      · obtain ⟨x₁, hx₁⟩ := htrue
        obtain ⟨S, hS, hScard⟩ := h1 x₁ hx₁
        -- the restricted dishes still satisfy the hypotheses, with `k` in place of `k+1`
        have hrestr : ∀ a : Pantry n, tasteCost (restrictDish f S a) ≤ k * m := by
          intro a
          refine ih _ ?_ ?_
          · intro z hz
            have hz' : f (fun j => if j ∈ S then a j else z j) = false := hz
            obtain ⟨T, hT, hTcard⟩ := h0 _ hz'
            refine ⟨T \ S, restrict_isCertificate hT, ?_⟩
            obtain ⟨i, hi⟩ := cert_inter_nonempty hS hT (by rw [hx₁, hz']; simp)
            obtain ⟨hiS, hiT⟩ := Finset.mem_inter.1 hi
            have hsub : T \ S ⊆ T.erase i := by
              intro j hj
              obtain ⟨hjT, hjS⟩ := Finset.mem_sdiff.1 hj
              exact Finset.mem_erase.2 ⟨fun hji => hjS (hji ▸ hiS), hjT⟩
            have hcard := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hiT] at hcard
            have hTpos : 1 ≤ T.card := Finset.card_pos.2 ⟨i, hiT⟩
            omega
          · intro z hz
            have hz' : f (fun j => if j ∈ S then a j else z j) = true := hz
            obtain ⟨T, hT, hTcard⟩ := h1 _ hz'
            exact ⟨T \ S, restrict_isCertificate hT,
              le_trans (Finset.card_le_card (Finset.sdiff_subset)) hTcard⟩
        choose t ht hd using fun a : Pantry n => exists_optimal_taste (restrictDish f S a)
        have hdepth : ∀ a, (t a).depth ≤ k * m := fun a => le_trans (hd a) (hrestr a)
        refine tasteCost_le_of_computes (t := queryList S.toList t (fun _ => false)) ?_ |>.trans ?_
        · intro x
          rw [queryList_eval]
          have := ht (fun j => if j ∈ S.toList then x j else false) x
          rw [this]
          simp only [restrictDish, Finset.mem_toList]
          congr 1
          funext j
          by_cases hj : j ∈ S <;> simp [hj]
        · refine le_trans (queryList_depth _ _ hdepth _) ?_
          rw [Finset.length_toList]
          have : S.card ≤ m := hScard
          calc S.card + k * m ≤ m + k * m := by omega
            _ = (k + 1) * m := by ring
      · push_neg at htrue
        have : ∀ y, f y = false := fun y => by
          cases hy : f y
          · rfl
          · exact absurd hy (htrue y)
        rw [(tasteCost_zero_iff_constant f).2 ⟨false, this⟩]
        exact Nat.zero_le _
