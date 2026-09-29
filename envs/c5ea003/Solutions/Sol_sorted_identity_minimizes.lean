-- Prove2me | solution 1 for sorted_identity_minimizes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:25:58.476333+00:00
-- url     : https://prove2.me/submissions/2d548fae-c18e-4461-b716-8f105d5b5f9b

-- Sol generated from Bridges/VoiceLeadingMonge.lean
import Mathlib
/-
# The Monge Uncrossing Lemma and Sorted Matching Optimality

This file proves the discrete rearrangement inequality for absolute value on ℤ:
for monotone sequences, sorted (identity) matching minimizes the total absolute
difference over all permutations.

## Main Results

* `abs_monge` — The four-point Monge inequality for |·| on ℤ.
* `sorted_identity_minimizes` — For monotone sequences, the identity permutation
  minimizes the sum of coordinatewise absolute differences.
-/


open Finset Equiv

/-! ## The Monge Inequality -/


/-! ## Main Theorem: Sorted Identity Minimizes Cost -/


set_option maxHeartbeats 800000 in

/-
**Rearrangement Theorem for ℤ.** For monotone (sorted) sequences x and y,
    the identity matching minimizes the sum of absolute differences over all
    permutations. This is the discrete 1D optimal transport theorem.
-/
theorem solution{n : ℕ} (x y : Fin n → ℤ)
    (hx : Monotone x) (hy : Monotone y) (σ : Equiv.Perm (Fin n)) :
    ∑ i : Fin n, Int.natAbs (x i - y i) ≤
    ∑ i : Fin n, Int.natAbs (x i - y (σ i)) := by
      have h_rearrangement : ∀ (n : ℕ) (x y : Fin n → ℤ) (hx : Monotone x) (hy : Monotone y) (σ : Perm (Fin n)), ∑ i : Fin n, (x i - y (σ i)).natAbs ≥ ∑ i : Fin n, (x i - y i).natAbs := by
        intro n;
        induction' n with n ih;
        · decide +kernel;
        · intro x y hx hy σ;
          -- Let $k = \sigma^{-1}(n)$, so $\sigma(k) = n$.
          obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), σ k = Fin.last n := by
            exact σ.surjective _;
          -- If $k = \text{Fin.last } n$, then $\sigma$ already fixes the last element.
          by_cases hk_last : k = Fin.last n;
          · -- Since $\sigma$ fixes the last element, we can restrict $\sigma$ to a permutation of $\{0, 1, ..., n-1\}$.
            obtain ⟨σ', hσ'⟩ : ∃ σ' : Perm (Fin n), ∀ i : Fin n, σ (Fin.castSucc i) = Fin.castSucc (σ' i) := by
              have h_restrict : ∀ i : Fin n, σ (Fin.castSucc i) ≠ Fin.last n := by
                intro i hi; have := σ.injective ( hi.trans hk.symm ) ; aesop;
              have h_restrict : ∀ i : Fin n, ∃ j : Fin n, σ (Fin.castSucc i) = Fin.castSucc j := by
                exact fun i => ⟨ ⟨ σ ( Fin.castSucc i ) |> Fin.val, lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using h_restrict i ) ⟩, by simp +decide [ Fin.ext_iff ] ⟩;
              choose f hf using h_restrict;
              have h_inj : Function.Injective f := by
                intro i j hij; have := σ.injective ( by aesop : σ ( Fin.castSucc i ) = σ ( Fin.castSucc j ) ) ; aesop;
              exact ⟨ Equiv.ofBijective f ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩, hf ⟩;
            rw [ Fin.sum_univ_castSucc, Fin.sum_univ_castSucc ];
            simp_all +decide [ Monotone ];
          · -- Define $\sigma'$ as $\sigma$ composed with the swap of $k$ and $\text{Fin.last } n$.
            set σ' : Perm (Fin (n + 1)) := σ * Equiv.swap k (Fin.last n);
            -- By the properties of the swap, we have $\sum_{i} |x_i - y_{\sigma'(i)}| \leq \sum_{i} |x_i - y_{\sigma(i)}|$.
            have h_swap : ∑ i, Int.natAbs (x i - y (σ' i)) ≤ ∑ i, Int.natAbs (x i - y (σ i)) := by
              have h_swap : Int.natAbs (x k - y (σ' k)) + Int.natAbs (x (Fin.last n) - y (σ' (Fin.last n))) ≤ Int.natAbs (x k - y (σ k)) + Int.natAbs (x (Fin.last n) - y (σ (Fin.last n))) := by
                simp +zetaDelta at *;
                rw [ hk ];
                cases abs_cases ( x k - y ( σ ( Fin.last n ) ) ) <;> cases abs_cases ( x ( Fin.last n ) - y ( Fin.last n ) ) <;> cases abs_cases ( x k - y ( Fin.last n ) ) <;> cases abs_cases ( x ( Fin.last n ) - y ( σ ( Fin.last n ) ) ) <;> linarith [ hx ( show k ≤ Fin.last n from Fin.le_last _ ), hy ( show σ ( Fin.last n ) ≤ Fin.last n from Fin.le_last _ ) ];
              have h_swap : ∑ i ∈ Finset.univ \ {k, Fin.last n}, Int.natAbs (x i - y (σ' i)) = ∑ i ∈ Finset.univ \ {k, Fin.last n}, Int.natAbs (x i - y (σ i)) := by
                refine' Finset.sum_congr rfl fun i hi => _;
                simp +zetaDelta at *;
                rw [ swap_apply_def ] ; aesop;
              simp_all +decide [ ← Finset.sum_sdiff ( Finset.subset_univ { k, Fin.last n } ) ];
            -- Since $\sigma'$ fixes the last element, we can apply the induction hypothesis to the restriction of $\sigma'$ to $\text{Fin } n$.
            have h_ind : ∑ i : Fin n, Int.natAbs (x (Fin.castSucc i) - y (σ' (Fin.castSucc i))) ≥ ∑ i : Fin n, Int.natAbs (x (Fin.castSucc i) - y (Fin.castSucc i)) := by
              have h_ind : ∃ σ'' : Perm (Fin n), ∀ i : Fin n, σ' (Fin.castSucc i) = Fin.castSucc (σ'' i) := by
                have h_ind : ∀ i : Fin n, σ' (Fin.castSucc i) ≠ Fin.last n := by
                  intro i hi; have := σ.injective ( hi.trans hk.symm ) ; simp_all +decide [ Fin.ext_iff, swap_apply_def ] ;
                  grind +splitImp;
                have h_ind : ∀ i : Fin n, ∃ j : Fin n, σ' (Fin.castSucc i) = Fin.castSucc j := by
                  exact fun i => ⟨ ⟨ σ' ( Fin.castSucc i ) |> Fin.val, lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using h_ind i ) ⟩, by simp +decide [ Fin.ext_iff ] ⟩;
                choose f hf using h_ind;
                have h_ind : Function.Injective f := by
                  intro i j hij; have := σ'.injective ( by aesop : σ' ( Fin.castSucc i ) = σ' ( Fin.castSucc j ) ) ; aesop;
                exact ⟨ Equiv.ofBijective f ⟨ h_ind, Finite.injective_iff_surjective.mp h_ind ⟩, hf ⟩;
              obtain ⟨ σ'', hσ'' ⟩ := h_ind; specialize ih ( fun i => x ( Fin.castSucc i ) ) ( fun i => y ( Fin.castSucc i ) ) ( fun i j hij => hx hij ) ( fun i j hij => hy hij ) σ''; aesop;
            have h_split : ∑ i : Fin (n + 1), Int.natAbs (x i - y (σ' i)) = ∑ i : Fin n, Int.natAbs (x (Fin.castSucc i) - y (σ' (Fin.castSucc i))) + Int.natAbs (x (Fin.last n) - y (σ' (Fin.last n))) := by
              exact Fin.sum_univ_castSucc _;
            have h_split' : ∑ i : Fin (n + 1), Int.natAbs (x i - y i) = ∑ i : Fin n, Int.natAbs (x (Fin.castSucc i) - y (Fin.castSucc i)) + Int.natAbs (x (Fin.last n) - y (Fin.last n)) := by
              exact Fin.sum_univ_castSucc _;
            simp +zetaDelta at *;
            grind;
      exact h_rearrangement n x y hx hy σ
