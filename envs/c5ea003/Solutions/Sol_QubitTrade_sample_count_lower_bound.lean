-- Prove2me | solution 1 for QubitTrade.sample_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:58:58.291548+00:00
-- url     : https://prove2.me/submissions/636b75aa-7086-42af-8e4f-1ac3ff89bb82

-- Sol generated from Algebra/QubitTrade/SampleComplexity.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Capacity

/-!
# QUBIT-TRADE VII: the exchange rate between qubits and samples

`Capacity.lean` shows that one truncated sample carries at most `t` bits (its
alphabet has `min (2^t) r` symbols).  Here we turn that into a *counting* lower
bound on the number of samples, which is the precise form of the observed
"qubit ↔ sample fungibility":

* `QubitTrade.sample_count_lower_bound` — if an estimator identifies every order
  in a family `S` from a record of `m` truncated samples, then `|S| ≤ (2^t)^m`,
  i.e. `m · t ≥ log₂ |S|`;
* `QubitTrade.sample_count_lower_bound_window` — applied to the collapse window
  `[2^t, R]` of `SupportCollapse.lean`: identifying an order below `R` costs
  `m · t ≥ log₂ (R - 2^t + 1)` — qubits and samples are exchangeable only through
  their *product*, never below the resolution threshold, where the right-hand side
  can never be met because the records themselves coincide.

The bound is unconditional and holds for arbitrary (even non-uniform,
computationally unbounded) post-processing.
-/

open QubitTrade

open Finset




open QubitTrade in
theorem solution{t m : ℕ} (S : Finset ℕ) (A : List ℕ → ℕ) (L : ℕ → List ℕ)
    (hlen : ∀ r ∈ S, (L r).length = m) (halph : ∀ r ∈ S, ∀ x ∈ L r, x < 2 ^ t)
    (hA : ∀ r ∈ S, A (L r) = r) :
    S.card ≤ (2 ^ t) ^ m := by
  classical
  set f : ℕ → (Fin m → ℕ) := fun r i => (L r).getD i 0 with hf
  have hmaps : ∀ r ∈ S, f r ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (2 ^ t)) := by
    intro r hr
    simp only [Fintype.mem_piFinset, Finset.mem_range, hf]
    intro i
    have hi : (i : ℕ) < (L r).length := by rw [hlen r hr]; exact i.2
    have : (L r).getD i 0 = (L r)[(i : ℕ)] := by
      rw [List.getD_eq_getElem _ _ hi]
    rw [this]
    exact halph r hr _ (List.getElem_mem hi)
  have hinj : Set.InjOn f S := by
    intro a ha b hb hab
    have hlist : L a = L b := by
      apply List.ext_getElem (by rw [hlen a ha, hlen b hb])
      intro n h1 h2
      have hn : n < m := by rw [← hlen a ha]; exact h1
      have h := congrFun hab ⟨n, hn⟩
      simp only [hf] at h
      rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at h
    calc a = A (L a) := (hA a ha).symm
      _ = A (L b) := by rw [hlist]
      _ = b := hA b hb
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  have hpi : (Fintype.piFinset (fun _ : Fin m => Finset.range (2 ^ t))).card = (2 ^ t) ^ m := by
    rw [Fintype.card_piFinset]
    simp
  omega
