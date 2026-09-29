-- Prove2me | solution 1 for fixed_cardinality_event_probability_monotone_of_event_mono
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T03:33:22.731147+00:00
-- url     : https://prove2.me/submissions/93ce8e3b-c3d3-4b40-8c3c-12c478b4006d

import Definitions.Def_matrix_completion_fixed_cardinality
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
open MatrixCompletion
open scoped Classical BigOperators
open Finset

namespace SolAux

/-- The filtered layer family: subsets of cardinality `m` satisfying `Event`. -/
noncomputable def layer {n₁ n₂ : ℕ} (m : ℕ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    Finset (Finset (Fin n₁ × Fin n₂)) :=
  (Finset.powersetCard m (Finset.univ : Finset (Fin n₁ × Fin n₂))).filter Event

/-- `fixedCardinalityEventProb m Event = #(layer m) / C(M, m)`. -/
theorem prob_eq {n₁ n₂ : ℕ} (m : ℕ) (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    fixedCardinalityEventProb m Event
      = ((layer m Event).card : ℝ) / ((n₁ * n₂).choose m : ℝ) := by
  unfold fixedCardinalityEventProb layer
  simp only
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]

/-- Lower bound on the number of upward neighbours of `a` in the next layer. -/
theorem above_lb {n₁ n₂ : ℕ} (Event : Finset (Fin n₁ × Fin n₂) → Prop)
    (hmono : ∀ A B : Finset (Fin n₁ × Fin n₂), A ⊆ B → Event A → Event B)
    (k : ℕ) (a : Finset (Fin n₁ × Fin n₂)) (ha : a ∈ layer k Event) :
    n₁ * n₂ - k ≤ ((layer (k+1) Event).bipartiteAbove (· ⊆ ·) a).card := by
  rw [layer, Finset.mem_filter, Finset.mem_powersetCard] at ha
  obtain ⟨⟨hasub, hacard⟩, haEv⟩ := ha
  have hcardc : (Finset.univ \ a).card = n₁ * n₂ - k := by
    rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ, hacard]
    simp [Fintype.card_prod]
  rw [← hcardc]
  apply Finset.card_le_card_of_injOn (fun x => insert x a)
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_sdiff] at hx
    rw [Finset.mem_coe, Finset.mem_bipartiteAbove]
    refine ⟨?_, Finset.subset_insert _ _⟩
    rw [layer, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨by simp, ?_⟩, ?_⟩
    · rw [Finset.card_insert_of_notMem hx.2, hacard]
    · exact hmono a (insert x a) (Finset.subset_insert _ _) haEv
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_sdiff] at hx hy
    simp only at hxy
    have hxa : x ∉ a := hx.2
    have : x ∈ insert y a := hxy ▸ Finset.mem_insert_self x a
    rcases Finset.mem_insert.mp this with h | h
    · exact h
    · exact absurd h hxa

/-- Upper bound on the number of downward neighbours of `b` in the previous layer. -/
theorem below_ub {n₁ n₂ : ℕ} (Event : Finset (Fin n₁ × Fin n₂) → Prop)
    (k : ℕ) (b : Finset (Fin n₁ × Fin n₂)) (hb : b ∈ layer (k+1) Event) :
    ((layer k Event).bipartiteBelow (· ⊆ ·) b).card ≤ k + 1 := by
  rw [layer, Finset.mem_filter, Finset.mem_powersetCard] at hb
  obtain ⟨⟨hbsub, hbcard⟩, hbEv⟩ := hb
  have hsub : (layer k Event).bipartiteBelow (· ⊆ ·) b ⊆ Finset.powersetCard k b := by
    intro s hs
    rw [Finset.mem_bipartiteBelow] at hs
    rw [Finset.mem_powersetCard]
    refine ⟨hs.2, ?_⟩
    rw [layer, Finset.mem_filter, Finset.mem_powersetCard] at hs
    exact hs.1.1.2
  calc ((layer k Event).bipartiteBelow (· ⊆ ·) b).card
      ≤ (Finset.powersetCard k b).card := Finset.card_le_card hsub
    _ = (b.card).choose k := Finset.card_powersetCard k b
    _ = (k+1).choose k := by rw [hbcard]
    _ = k + 1 := by rw [Nat.choose_succ_self_right]

/-- Adjacent-layer cardinality inequality (double counting). -/
theorem card_step {n₁ n₂ : ℕ} (Event : Finset (Fin n₁ × Fin n₂) → Prop)
    (hmono : ∀ A B : Finset (Fin n₁ × Fin n₂), A ⊆ B → Event A → Event B)
    (k : ℕ) :
    (layer k Event).card * (n₁ * n₂ - k)
      ≤ (layer (k+1) Event).card * (k + 1) := by
  classical
  exact card_mul_le_card_mul (· ⊆ ·)
    (fun a ha => above_lb Event hmono k a ha)
    (fun b hb => below_ub Event k b hb)

/-- Single-step probability monotonicity. -/
theorem prob_step {n₁ n₂ : ℕ} (Event : Finset (Fin n₁ × Fin n₂) → Prop)
    (hmono : ∀ A B : Finset (Fin n₁ × Fin n₂), A ⊆ B → Event A → Event B)
    (k : ℕ) (hk : k + 1 ≤ n₁ * n₂) :
    fixedCardinalityEventProb k Event ≤ fixedCardinalityEventProb (k+1) Event := by
  rw [prob_eq, prob_eq]
  set M := n₁ * n₂ with hM
  have hcard := card_step Event hmono k
  -- Nat identity: C(M,k) * (M - k) = C(M, k+1) * (k+1)
  have hkM : k ≤ M := Nat.le_of_succ_le hk
  have hchoose : M.choose k * (M - k) = M.choose (k+1) * (k+1) :=
    (Nat.choose_succ_right_eq M k).symm
  -- Now derive the real inequality.
  have hCkpos : (0:ℝ) < (M.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkM
  have hCk1pos : (0:ℝ) < (M.choose (k+1) : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  rw [div_le_div_iff₀ hCkpos hCk1pos]
  -- Goal: #layer k * C(M,k+1) ≤ #layer (k+1) * C(M,k)
  -- From hcard: #layer k * (M-k) ≤ #layer (k+1) * (k+1)
  -- Multiply both sides appropriately using hchoose.
  have hMk1 : k + 1 ≤ M := hk
  rcases Nat.eq_or_lt_of_le hkM with hkeq | hklt
  · -- k = M: then M - k = 0 and k+1 > M, contradiction with hk
    omega
  · -- k < M, so M - k ≥ 1
    have hMkpos : 1 ≤ M - k := by omega
    -- Cast hcard and hchoose to ℝ
    have hcardR : ((layer k Event).card : ℝ) * ((M - k : ℕ) : ℝ)
        ≤ ((layer (k+1) Event).card : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcard
    have hchooseR : (M.choose k : ℝ) * ((M - k : ℕ) : ℝ)
        = (M.choose (k+1) : ℝ) * ((k+1 : ℕ) : ℝ) := by
      exact_mod_cast hchoose
    -- multiply hcardR by C(M,k); use hchooseR to substitute
    have hpos1 : (0:ℝ) < ((M - k : ℕ) : ℝ) := by
      have : 0 < M - k := by omega
      exact_mod_cast this
    -- (#L_k * (M-k)) * C(M,k) ≤ (#L_{k+1} * (k+1)) * C(M,k)
    have step1 : ((layer k Event).card : ℝ) * ((M - k : ℕ):ℝ) * (M.choose k:ℝ)
        ≤ ((layer (k+1) Event).card:ℝ) * ((k+1:ℕ):ℝ) * (M.choose k:ℝ) := by
      apply mul_le_mul_of_nonneg_right hcardR (le_of_lt hCkpos)
    -- rearrange LHS: #L_k * C(M,k+1)*(k+1) and RHS: #L_{k+1}*(k+1)*C(M,k)
    -- LHS = #L_k * (C(M,k)*(M-k)) = #L_k * (C(M,k+1)*(k+1))
    have lhs_eq : ((layer k Event).card : ℝ) * ((M - k : ℕ):ℝ) * (M.choose k:ℝ)
        = ((layer k Event).card:ℝ) * (M.choose (k+1):ℝ) * ((k+1:ℕ):ℝ) := by
      rw [mul_assoc, mul_comm ((M - k : ℕ):ℝ) (M.choose k:ℝ), hchooseR]; ring
    rw [lhs_eq] at step1
    -- Cancel (k+1) > 0 from both sides
    have hk1pos : (0:ℝ) < ((k+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos k
    nlinarith [step1, hk1pos, mul_pos hk1pos hCkpos]

/-- Probability monotonicity over an arbitrary gap, by induction. -/
theorem prob_mono {n₁ n₂ : ℕ} (Event : Finset (Fin n₁ × Fin n₂) → Prop)
    (hmono : ∀ A B : Finset (Fin n₁ × Fin n₂), A ⊆ B → Event A → Event B)
    (k : ℕ) : ∀ d : ℕ, k + d ≤ n₁ * n₂ →
      fixedCardinalityEventProb k Event ≤ fixedCardinalityEventProb (k + d) Event := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
      intro hd
      have hstep : fixedCardinalityEventProb (k + d) Event
          ≤ fixedCardinalityEventProb (k + d + 1) Event :=
        prob_step Event hmono (k + d) (by omega)
      have hprev : fixedCardinalityEventProb k Event
          ≤ fixedCardinalityEventProb (k + d) Event := ih (by omega)
      calc fixedCardinalityEventProb k Event
          ≤ fixedCardinalityEventProb (k + d) Event := hprev
        _ ≤ fixedCardinalityEventProb (k + d + 1) Event := hstep
        _ = fixedCardinalityEventProb (k + (d + 1)) Event := by ring_nf

end SolAux

theorem solution
    {n₁ n₂ : ℕ} (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    (∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' → Event Omega → Event Omega') →
    ∀ k m : ℕ, k ≤ m → m ≤ n₁ * n₂ →
      fixedCardinalityEventProb k Event ≤
        fixedCardinalityEventProb m Event := by
  intro hmono k m hkm hmn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  exact SolAux.prob_mono Event hmono k d hmn
