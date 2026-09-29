-- Prove2me | Definitions.Def_mme_fractional_rank
-- name    : mme_fractional_rank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T15:33:45.603501+00:00
-- url     : https://prove2.me/theorems/444c00cd-6f19-4a9d-addd-4d6de2d67948
-- statement:
--   **Fractional rank $\rho$ and fractional subrank $\kappa$ — real-valued relaxations of integer rank/subrank.**
--
--   Port of the Prism `AsymptoticSpectra/Rank.lean` development to the native `MME.StrassenPreorder` structure. Sorry-free, self-contained on Mathlib + MME's `Def_mme_strassen_preorder` and `Def_mme_spectrum`.
--
--   **Definitions.** For a Strassen preorder $P$ on a `CommSemiring` $R$ and $a \in R$:
--   $$\rho(a) \;=\; \inf \Bigl\{ \tfrac{n}{m} \;:\; m \cdot a \leq_P n,\; m \geq 1 \Bigr\}, \quad\quad \kappa(a) \;=\; \sup \Bigl\{ \tfrac{n}{m} \;:\; n \leq_P m \cdot a,\; m \geq 1 \Bigr\}.$$
--   Geometrically, $\rho$ "smooths out" integer rank by allowing repeated copies — a single object that needs slightly more than $n$ units of resource can use $m$ copies that need slightly less than $mn$, picking up a sharper bound in the rational limit.
--
--   **Headline result.** `rho_toRingHom`: for a **total** Strassen preorder $P$ (e.g., the maximal Zornian extension), $\rho : R \to \mathbb{R}$ is a **semiring homomorphism**:
--   $$\rho(a + b) = \rho(a) + \rho(b), \quad \rho(a \cdot b) = \rho(a) \cdot \rho(b), \quad \rho(0) = 0, \quad \rho(1) = 1.$$
--   The reverse inequalities $\rho(a+b) \geq \rho(a)+\rho(b)$ and $\rho(ab) \geq \rho(a)\rho(b)$ depend on totality (via $\rho = \kappa$ in the total case). With monotonicity, this exhibits $\rho$ as an **asymptotic spectrum point**, supplying the existence half of Strassen duality.
--
--   **Implementation note.** Prism's `rank` is `Nat.find`-based; MME's is `sInf`-based, so we use MME's `le_rank` / `rank_le_of_le` where Prism uses `Nat.find_spec` / `Nat.find_min'`. The submultiplicative / relative-rank scaffolding from Prism is not ported (not needed for the MME duality argument).

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Definitions.Def_mme_strassen_preorder
import Definitions.Def_mme_spectrum

/-! # Fractional rank `ρ` and fractional subrank `κ` (MME)

Port of the Prism `AsymptoticSpectra/Rank.lean` development of fractional rank to the
native `MME.StrassenPreorder` structure. Following Wigderson–Zuiddam, the **fractional
rank** `ρ(a) = inf { n/m | m·a ≤ n }` and the **fractional subrank**
`κ(a) = sup { n/m | n ≤ m·a }` are real-valued relaxations of integer rank/subrank.

The headline result is `rho_toRingHom`: for a **total** Strassen preorder, `ρ` is a
semiring homomorphism `R →+* ℝ` — it is additive and multiplicative (the reverse
inequalities `rho_add` / `rho_mul` use totality via `ρ = κ`).

Prism's `rank` is `Nat.find`-based; MME's is `sInf`-based, so where Prism uses
`Nat.find_spec` / `Nat.find_min'` we use MME's `le_rank` / `rank_le_of_le`. The whole
`rho`/`kappa` chain is independent of Prism's `IsSubmultiplicative` / `relative_rank`
machinery, so none of that is ported here.

Self-contained on Mathlib plus MME's `Def_mme_strassen_preorder` and `Def_mme_spectrum`.
Sorry-free. -/

universe u

noncomputable section

open Classical

namespace MME

namespace StrassenPreorder

variable {R : Type u} [CommSemiring R] (P : StrassenPreorder R)

/-- `a * b ≠ 0` from the no-zero-divisors structure carried by any Strassen preorder. -/
theorem mul_ne_zero (P : StrassenPreorder R) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 :=
  letI := P.toNoZeroDivisors
  _root_.mul_ne_zero ha hb

/-! ## Integer subrank -/

/-- A predicate `Q` has a greatest natural-number witness at `n`. -/
def IsGreatestNat (Q : ℕ → Prop) (n : ℕ) : Prop :=
  Q n ∧ ∀ m, Q m → m ≤ n

/-- The data witnessing the subrank: the greatest `n` with `n ≤ a`. -/
def subrankData (P : StrassenPreorder R) (a : R) :
    { n : ℕ // IsGreatestNat (fun n => P.le n a) n } := by
  let S := fun (n : ℕ) => P.le (n : R) a
  haveI : DecidablePred S := Classical.decPred S
  let bound := rank P a + 1
  -- We search for the greatest n < bound satisfying S
  let n := Nat.findGreatest S bound
  have h_bound : S 0 := by
    dsimp [S]
    rw [Nat.cast_zero]
    exact P.zero_le a
  have h_S : S n := Nat.findGreatest_spec (Nat.zero_le _) h_bound
  have h_n_le_rank : n ≤ rank P a := by
    dsimp [S] at h_S
    have h_le_rank := le_rank P a
    have := P.le_trans _ _ _ h_S h_le_rank
    rwa [P.nat_order_embedding] at this
  have h_n_bound : n < bound := Nat.lt_succ_of_le h_n_le_rank
  refine ⟨n, ?_, ?_⟩
  · exact h_S
  · intro m hm
    -- If m satisfies S, then m < bound because m ≤ a ≤ rank a < bound
    have h_m_bound : m < bound := by
      rw [Nat.lt_succ_iff]
      -- m ≤ a and a ≤ rank a implies m ≤ rank a
      have h_a_rank : P.le a (rank P a) := le_rank P a
      have h_m_rank : P.le m (rank P a) := P.le_trans _ _ _ hm h_a_rank
      rwa [P.nat_order_embedding] at h_m_rank
    exact Nat.le_findGreatest (Nat.le_of_lt h_m_bound) hm

/-- The subrank of an element is the largest natural number n such that n ≤ a. -/
def subrank (P : StrassenPreorder R) (a : R) : ℕ :=
  (subrankData P a).1

theorem le_subrank (P : StrassenPreorder R) (a : R) : P.le (subrank P a) a :=
  (subrankData P a).2.1

theorem subrank_maximal (P : StrassenPreorder R) (a : R) (n : ℕ) (h : P.le n a) :
    n ≤ subrank P a :=
  (subrankData P a).2.2 n h

theorem subrank_le_iff (P : StrassenPreorder R) (a : R) (n : ℕ) :
    n ≤ subrank P a ↔ P.le n a := by
  constructor
  · intro h
    exact P.le_trans _ _ _ (P.nat_order_embedding _ _ |>.mpr h) (le_subrank P a)
  · exact subrank_maximal P a n

theorem subrank_le_rank (P : StrassenPreorder R) (a : R) : subrank P a ≤ rank P a := by
  have h1 : P.le (subrank P a) a := le_subrank P a
  have h2 : P.le a (rank P a) := le_rank P a
  have h3 : P.le (subrank P a) (rank P a) := P.le_trans _ _ _ h1 h2
  rwa [P.nat_order_embedding] at h3

theorem subrank_monotone (P : StrassenPreorder R) (a : R) (b : R) (h : P.le a b) :
    subrank P a ≤ subrank P b := by
  apply subrank_maximal
  apply P.le_trans _ a
  · exact le_subrank P a
  · exact h

theorem subrank_superadditive (P : StrassenPreorder R) (a : R) (b : R) :
    subrank P (a + b) ≥ subrank P a + subrank P b := by
  apply subrank_maximal
  rw [Nat.cast_add]
  letI := P.toPreorder
  apply P.le_trans _ (subrank P a + b)
  · rw [add_comm]
    nth_rewrite 2 [add_comm]
    apply P.add_right
    exact le_subrank P b
  · apply P.add_right
    exact le_subrank P a

theorem subrank_supermultiplicative (P : StrassenPreorder R) (a : R) (b : R) :
    subrank P (a * b) ≥ subrank P a * subrank P b := by
  apply subrank_maximal
  rw [Nat.cast_mul]
  letI := P.toPreorder
  apply P.le_trans _ (subrank P a * b)
  · rw [mul_comm]
    nth_rewrite 2 [mul_comm]
    apply P.mul_right
    exact le_subrank P b
  · apply P.mul_right
    exact le_subrank P a

/-! ## Fractional rank `ρ` and fractional subrank `κ` -/

/-- The set of rational upper bounds for fractional rank. -/
def rho_set (P : StrassenPreorder R) (a : R) : Set ℝ :=
  { q : ℝ | ∃ (n m : ℕ), 0 < m ∧ P.le (m * a) n ∧ q = (n : ℝ) / m }

/-- The set of rational lower bounds for fractional subrank. -/
def kappa_set (P : StrassenPreorder R) (a : R) : Set ℝ :=
  { q : ℝ | ∃ (n m : ℕ), 0 < m ∧ P.le n (m * a) ∧ q = (n : ℝ) / m }

/-- The fractional rank of an element. -/
def rho (P : StrassenPreorder R) (a : R) : ℝ := sInf (P.rho_set a)

/-- The fractional subrank of an element. -/
def kappa (P : StrassenPreorder R) (a : R) : ℝ := sSup (P.kappa_set a)

lemma rho_set_nonempty (P : StrassenPreorder R) (a : R) : (P.rho_set a).Nonempty := by
  obtain ⟨n, hn⟩ := P.upper_archimedean a
  refine ⟨(n : ℝ), n, 1, Nat.zero_lt_one, ?_, by simp⟩
  simpa using hn

lemma rho_set_bddBelow (P : StrassenPreorder R) (a : R) : BddBelow (P.rho_set a) := by
  use 0
  rintro q ⟨n, m, hm, _, rfl⟩
  apply div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)

lemma kappa_set_nonempty (P : StrassenPreorder R) (a : R) : (P.kappa_set a).Nonempty := by
  refine ⟨0, 0, 1, Nat.zero_lt_one, ?_, by simp⟩
  simp; exact P.zero_le a

lemma kappa_set_bddAbove (P : StrassenPreorder R) (a : R) : BddAbove (P.kappa_set a) := by
  obtain ⟨K, hK⟩ := P.upper_archimedean a
  use K
  rintro q ⟨n, m, hm, h, rfl⟩
  rw [div_le_iff₀ (Nat.cast_pos.mpr hm)]
  norm_cast
  have h_ma_mK : P.le ((m : R) * a) ((m : R) * (K : R)) := by
    rw [mul_comm, mul_comm (m : R) (K : R)]
    apply P.mul_right a (K : R) hK (m : R)
  rw [mul_comm K m]
  apply (P.nat_order_embedding n (m * K)).mp
  rw [Nat.cast_mul]
  exact P.le_trans _ _ _ h h_ma_mK

/-! ## `sInf`/`sSup` arithmetic helpers -/

lemma sInf_add_sInf_le {S1 S2 S3 : Set ℝ} (h1 : S1.Nonempty) (h2 : S2.Nonempty)
    (H : ∀ x ∈ S1, ∀ y ∈ S2, sInf S3 ≤ x + y) : sInf S3 ≤ sInf S1 + sInf S2 := by
  have h_y : ∀ y ∈ S2, sInf S3 - y ≤ sInf S1 := by
    intro y hy
    apply le_csInf h1
    intro x hx
    linarith [H x hx y hy]
  have h_x : sInf S3 - sInf S1 ≤ sInf S2 := by
    apply le_csInf h2
    intro y hy
    linarith [h_y y hy]
  linarith

lemma sInf_mul_sInf_le {S1 S2 S3 : Set ℝ} (h1 : S1.Nonempty) (hb1 : BddBelow S1)
    (pos1 : ∀ x ∈ S1, 0 ≤ x) (h2 : S2.Nonempty) (pos2 : ∀ x ∈ S2, 0 ≤ x)
    (H : ∀ x ∈ S1, ∀ y ∈ S2, sInf S3 ≤ x * y) : sInf S3 ≤ sInf S1 * sInf S2 := by
  have h_inf1 : 0 ≤ sInf S1 := le_csInf h1 pos1
  by_cases h01 : sInf S1 = 0
  · rw [h01, zero_mul]
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y, hy⟩ := h2
    have h_nonneg_y : 0 ≤ y := pos2 y hy
    by_cases hy0 : y = 0
    · obtain ⟨x, hx⟩ := h1
      have := H x hx y hy
      rw [hy0, mul_zero] at this
      linarith
    · have : sInf S1 < sInf S1 + ε / y :=
        lt_add_of_pos_right _ (div_pos hε (lt_of_le_of_ne h_nonneg_y (Ne.symm hy0)))
      obtain ⟨x, hx, hx_lt⟩ := (csInf_lt_iff hb1 h1).mp this
      calc sInf S3 ≤ x * y := H x hx y hy
        _ ≤ (sInf S1 + ε / y) * y := mul_le_mul_of_nonneg_right hx_lt.le h_nonneg_y
        _ = ε := by field_simp [hy0]; rw [h01]; ring
        _ ≤ 0 + ε := by simp
  · have h1_pos : 0 < sInf S1 := lt_of_le_of_ne h_inf1 (Ne.symm h01)
    have h_bound : ∀ y ∈ S2, sInf S3 ≤ y * sInf S1 := by
      intro y hy
      by_cases hy0 : y = 0
      · rw [hy0, zero_mul]; obtain ⟨x, hx⟩ := h1; have := H x hx y hy
        rwa [hy0, mul_zero] at this
      · have : 0 < y := lt_of_le_of_ne (pos2 y hy) (Ne.symm hy0)
        rw [mul_comm y]
        apply (div_le_iff₀ this).mp
        apply le_csInf h1
        intro x hx
        apply (div_le_iff₀ this).mpr
        exact H x hx y hy
    have : ∀ y ∈ S2, sInf S3 / sInf S1 ≤ y := by
      intro y hy
      exact (div_le_iff₀ h1_pos).mpr (h_bound y hy)
    have : sInf S3 / sInf S1 ≤ sInf S2 := le_csInf h2 this
    rw [mul_comm]
    exact (div_le_iff₀ h1_pos).mp this

lemma csSup_add_le_csSup {S1 S2 S3 : Set ℝ} (h1 : S1.Nonempty) (h2 : S2.Nonempty)
    (H : ∀ x ∈ S1, ∀ y ∈ S2, x + y ≤ sSup S3) : sSup S1 + sSup S2 ≤ sSup S3 := by
  have h_y : ∀ y ∈ S2, sSup S1 ≤ sSup S3 - y := by
    intro y hy
    apply csSup_le h1
    intro x hx
    linarith [H x hx y hy]
  have h_x : sSup S2 ≤ sSup S3 - sSup S1 := by
    apply csSup_le h2
    intro y hy
    linarith [h_y y hy]
  linarith

lemma csSup_mul_le_csSup {S1 S2 S3 : Set ℝ} (h1 : S1.Nonempty) (hb1 : BddAbove S1)
    (pos1 : ∀ x ∈ S1, 0 ≤ x) (h2 : S2.Nonempty) (pos2 : ∀ x ∈ S2, 0 ≤ x)
    (H : ∀ x ∈ S1, ∀ y ∈ S2, x * y ≤ sSup S3) : sSup S1 * sSup S2 ≤ sSup S3 := by
  have h_nonneg_sup1 : 0 ≤ sSup S1 := (pos1 h1.some h1.some_mem).trans (le_csSup hb1 h1.some_mem)
  by_cases h01 : sSup S1 = 0
  · rw [h01, zero_mul]
    obtain ⟨x, hx⟩ := h1
    obtain ⟨y, hy⟩ := h2
    have : 0 ≤ x * y := mul_nonneg (pos1 x hx) (pos2 y hy)
    exact this.trans (H x hx y hy)
  · have h1_pos : 0 < sSup S1 := lt_of_le_of_ne h_nonneg_sup1 (Ne.symm h01)
    have h_bound : ∀ y ∈ S2, y * sSup S1 ≤ sSup S3 := by
        intro y hy
        by_cases hy0 : y = 0
        · rw [hy0, zero_mul]; obtain ⟨x, hx⟩ := h1; have := H x hx y hy
          rwa [hy0, mul_zero] at this
        · have hy_pos : 0 < y := lt_of_le_of_ne (pos2 y hy) (Ne.symm hy0)
          rw [mul_comm y]
          apply (le_div_iff₀ hy_pos).mp
          apply csSup_le h1
          intro x hx
          apply (le_div_iff₀ hy_pos).mpr
          exact H x hx y hy
    have : ∀ y ∈ S2, y ≤ sSup S3 / sSup S1 := by
      intro y hy
      exact (le_div_iff₀ h1_pos).mpr (h_bound y hy)
    have : sSup S2 ≤ sSup S3 / sSup S1 := csSup_le h2 this
    rw [mul_comm]
    exact (le_div_iff₀ h1_pos).mp this

/-! ## `ρ` is monotone, sub-additive and sub-multiplicative -/

theorem rho_monotone (P : StrassenPreorder R) {a b : R} (h : P.le a b) : P.rho a ≤ P.rho b := by
  apply le_csInf (P.rho_set_nonempty b)
  rintro q ⟨n, m, hm, hb, rfl⟩
  apply csInf_le (P.rho_set_bddBelow a)
  refine ⟨n, m, hm, ?_, rfl⟩
  have h_ma_mb : P.le ((m : R) * a) ((m : R) * b) := by
    rw [mul_comm, mul_comm (m : R) b]
    apply P.mul_right a b h (m : R)
  exact P.le_trans _ _ _ h_ma_mb hb

theorem rho_nat_cast (P : StrassenPreorder R) (n : ℕ) : P.rho n = n := by
  apply le_antisymm
  · apply csInf_le (P.rho_set_bddBelow n)
    refine ⟨n, 1, Nat.zero_lt_one, ?_, by simp⟩
    simp only [Nat.cast_one, one_mul, P.le_refl]
  · apply le_csInf (P.rho_set_nonempty n)
    rintro q ⟨k, m, hm, h, rfl⟩
    rw [le_div_iff₀ (Nat.cast_pos.mpr hm)]
    norm_cast at h
    rw [Nat.mul_comm] at h
    norm_cast
    exact (P.nat_order_embedding _ _).mp h

theorem rho_add_le (P : StrassenPreorder R) (a b : R) : P.rho (a + b) ≤ P.rho a + P.rho b := by
  apply sInf_add_sInf_le (P.rho_set_nonempty a) (P.rho_set_nonempty b)
  rintro q1 ⟨n1, m1, hm1, ha, rfl⟩ q2 ⟨n2, m2, hm2, hb, rfl⟩
  apply csInf_le (P.rho_set_bddBelow _)
  refine ⟨m2 * n1 + m1 * n2, m1 * m2, Nat.mul_pos hm1 hm2, ?_, ?_⟩
  · have h_eq1 : (↑(m1 * m2) * (a + b) : R) = (↑m1 * a) * ↑m2 + (↑m2 * b) * ↑m1 := by
      push_cast; ring
    rw [h_eq1]
    have hA : P.le (↑m1 * a * ↑m2) (↑n1 * ↑m2) := by
      apply P.mul_right (↑m1 * a) (↑n1) ha
    have hB : P.le (↑m2 * b * ↑m1) ((n2 : R) * m1) := by
      apply P.mul_right
      exact hb
    letI := P.toPreorder
    calc
      P.le ((↑m1 * a) * ↑m2 + (↑m2 * b) * ↑m1) (↑n1 * ↑m2 + (↑m2 * b) * ↑m1) := by
        apply P.add_right; exact hA
      _ ≤ ↑n1 * ↑m2 + (n2 : R) * m1 := by
        have h_comm : ↑n1 * ↑m2 + ↑m2 * b * ↑m1 = ↑m2 * b * ↑m1 + ↑n1 * ↑m2 := by ring
        have h_comm2 : ↑n1 * ↑m2 + (n2 : R) * m1 = (n2 : R) * m1 + ↑n1 * ↑m2 := by ring
        rw [h_comm, h_comm2]
        apply P.add_right; exact hB
      _ ≤ ↑(m2 * n1 + m1 * n2) := by
        apply le_of_eq; push_cast; ring
  · push_cast; field_simp; try ring

theorem rho_mul_le (P : StrassenPreorder R) (a b : R) : P.rho (a * b) ≤ P.rho a * P.rho b := by
  let Sa := P.rho_set a
  let Sb := P.rho_set b
  have posa : ∀ q ∈ Sa, 0 ≤ q := by
    rintro q ⟨n, m, hm, h, rfl⟩; apply div_nonneg <;> exact Nat.cast_nonneg _
  have posb : ∀ q ∈ Sb, 0 ≤ q := by
    rintro q ⟨n, m, hm, h, rfl⟩; apply div_nonneg <;> exact Nat.cast_nonneg _
  apply sInf_mul_sInf_le (P.rho_set_nonempty a) (P.rho_set_bddBelow a) posa
    (P.rho_set_nonempty b) posb
  rintro q1 ⟨n1, m1, hm1, ha, rfl⟩ q2 ⟨n2, m2, hm2, hb, rfl⟩
  apply csInf_le (P.rho_set_bddBelow _)
  refine ⟨n1 * n2, m1 * m2, Nat.mul_pos hm1 hm2, ?_, ?_⟩
  · letI := P.toPreorder
    have h_eq : ↑(m1 * m2) * (a * b) = (↑m1 * a) * (↑m2 * b) := by push_cast; ring
    rw [h_eq]
    calc
      P.le ((↑m1 * a) * (↑m2 * b)) (↑n1 * (↑m2 * b)) := by
        exact P.mul_right (↑m1 * a) (↑n1) ha (↑m2 * b)
      _ ≤ ↑n1 * ↑n2 := by
        have h_swap : ↑n1 * (↑m2 * b) = (↑m2 * b) * ↑n1 := by ring
        rw [h_swap]
        have h_main : P.le ((↑m2 * b) * ↑n1) (↑n2 * ↑n1) := P.mul_right (↑m2 * b) (↑n2) hb (↑n1)
        have h_comm_res : (↑n2 : R) * ↑n1 = ↑n1 * ↑n2 := by ring
        rw [← h_comm_res]
        exact h_main
      _ ≤ ↑(n1 * n2) := by
        apply le_of_eq; push_cast; rfl
  · push_cast; field_simp; try ring

/-! ## `κ` is monotone, super-additive and super-multiplicative -/

theorem kappa_monotone (P : StrassenPreorder R) {a b : R} (h : P.le a b) :
    P.kappa a ≤ P.kappa b := by
  apply csSup_le (P.kappa_set_nonempty a)
  rintro q ⟨n, m, hm, ha, rfl⟩
  apply le_csSup (P.kappa_set_bddAbove b)
  refine ⟨n, m, hm, ?_, rfl⟩
  have h_ma : P.le ((m : R) * a) ((m : R) * b) := by
    rw [mul_comm, mul_comm (m : R) b]
    apply P.mul_right a b h (m : R)
  exact P.le_trans _ _ _ ha h_ma

theorem kappa_nat_cast (P : StrassenPreorder R) (n : ℕ) : P.kappa n = n := by
  apply le_antisymm
  · apply csSup_le (P.kappa_set_nonempty n)
    rintro q ⟨k, m, hm, h, rfl⟩
    rw [div_le_iff₀ (Nat.cast_pos.mpr hm)]
    norm_cast at h
    rw [Nat.mul_comm] at h
    norm_cast
    exact (P.nat_order_embedding _ _).mp h
  · apply le_csSup (P.kappa_set_bddAbove n)
    refine ⟨n, 1, Nat.zero_lt_one, ?_, by simp⟩
    simp only [Nat.cast_one, one_mul, P.le_refl]

theorem kappa_add_ge (P : StrassenPreorder R) (a b : R) : P.kappa a + P.kappa b ≤ P.kappa (a + b) := by
  apply csSup_add_le_csSup (P.kappa_set_nonempty a) (P.kappa_set_nonempty b)
  rintro q1 ⟨n1, m1, hm1, ha, rfl⟩ q2 ⟨n2, m2, hm2, hb, rfl⟩
  apply le_csSup (P.kappa_set_bddAbove _)
  refine ⟨m2 * n1 + m1 * n2, m1 * m2, Nat.mul_pos hm1 hm2, ?_, ?_⟩
  · have h_eq1 : (↑(m1 * m2) * (a + b) : R) = (↑m1 * a) * ↑m2 + (↑m2 * b) * ↑m1 := by
      push_cast; ring
    rw [h_eq1]
    push_cast
    letI := P.toPreorder
    have hA : (↑m2 : R) * ↑n1 ≤ ↑m1 * a * ↑m2 := by
      have h1 : (↑m2 : R) * ↑n1 = ↑n1 * ↑m2 := by ring
      have h2 : ↑m1 * a * ↑m2 = (↑m1 * a) * ↑m2 := by ring
      rw [h1, h2]
      apply P.mul_right; exact ha
    have hB : (↑m1 : R) * ↑n2 ≤ ↑m2 * b * ↑m1 := by
      have h1 : (↑m1 : R) * ↑n2 = ↑n2 * ↑m1 := by ring
      have h2 : ↑m2 * b * ↑m1 = (↑m2 * b) * ↑m1 := by ring
      rw [h1, h2]
      apply P.mul_right; exact hb
    calc
      P.le (↑m2 * ↑n1 + ↑m1 * ↑n2) (↑m1 * a * ↑m2 + ↑m1 * ↑n2) := by
        apply P.add_right; exact hA
      _ ≤ ↑m1 * a * ↑m2 + ↑m2 * b * ↑m1 := by
        rw [add_comm, add_comm (↑m1 * a * ↑m2)]
        apply P.add_right; exact hB
  · push_cast; field_simp; try ring

theorem kappa_mul_ge (P : StrassenPreorder R) (a b : R) : P.kappa a * P.kappa b ≤ P.kappa (a * b) := by
  let Sa := P.kappa_set a
  let Sb := P.kappa_set b
  have posa : ∀ q ∈ Sa, 0 ≤ q := by
    rintro q ⟨n, m, hm, h, rfl⟩; apply div_nonneg <;> exact Nat.cast_nonneg _
  have posb : ∀ q ∈ Sb, 0 ≤ q := by
    rintro q ⟨n, m, hm, h, rfl⟩; apply div_nonneg <;> exact Nat.cast_nonneg _
  apply csSup_mul_le_csSup (P.kappa_set_nonempty a) (P.kappa_set_bddAbove a) posa
    (P.kappa_set_nonempty b) posb
  rintro q1 ⟨n1, m1, hm1, ha, rfl⟩ q2 ⟨n2, m2, hm2, hb, rfl⟩
  apply le_csSup (P.kappa_set_bddAbove _)
  refine ⟨n1 * n2, m1 * m2, Nat.mul_pos hm1 hm2, ?_, ?_⟩
  · letI := P.toPreorder
    push_cast
    calc
      P.le (↑n1 * ↑n2) (↑m1 * a * ↑n2) := by
        apply P.mul_right; exact ha
      _ ≤ ((↑m2 * b) * (↑m1 * a)) := by
        have h_comm : ↑m1 * a * ↑n2 = ↑n2 * (↑m1 * a) := by ring
        rw [h_comm]
        apply P.mul_right; exact hb
      _ ≤ (↑m1 * ↑m2 * (a * b)) := by
        apply le_of_eq; ring
  · push_cast; field_simp; try ring

/-! ## `κ ≤ ρ`, with equality under totality -/

theorem kappa_le_rho (P : StrassenPreorder R) (a : R) : P.kappa a ≤ P.rho a := by
  apply csSup_le (P.kappa_set_nonempty a)
  rintro qk ⟨nk, mk, hmk, hk, rfl⟩
  apply le_csInf (P.rho_set_nonempty a)
  rintro qr ⟨nr, mr, hmr, hr, rfl⟩
  have hmk_pos : 0 < (mk : ℝ) := Nat.cast_pos.mpr hmk
  have hmr_pos : 0 < (mr : ℝ) := Nat.cast_pos.mpr hmr
  rw [div_le_div_iff₀ hmk_pos hmr_pos]
  norm_cast
  letI := P.toPreorder
  -- Goal: nk * mr ≤ mk * nr
  have h1 : P.le (↑nk * ↑mr) (↑mk * a * ↑mr) := P.mul_right ↑nk (↑mk * a) hk ↑mr
  have h2 : P.le (↑mk * (↑mr * a)) (↑mk * ↑nr) := by
    apply P.le_trans _ ((↑mr * a) * ↑mk)
    · apply le_of_eq; ring
    · apply P.le_trans _ (↑nr * ↑mk)
      · exact P.mul_right (↑mr * a) ↑nr hr ↑mk
      · apply le_of_eq; ring
  have h_goal : P.le (↑nk * ↑mr) (↑mk * ↑nr) := by
    have h_eq : (↑mk : R) * a * ↑mr = ↑mk * (↑mr * a) := by ring
    rw [h_eq] at h1
    exact P.le_trans _ _ _ h1 h2
  rw [← Nat.cast_mul, ← Nat.cast_mul, P.nat_order_embedding] at h_goal
  rw [Nat.mul_comm nr mk]
  exact h_goal

theorem rho_eq_kappa_of_total (P : StrassenPreorder R) (total : P.IsTotal) (a : R) :
    P.rho a = P.kappa a := by
  apply le_antisymm
  · -- rho a ≤ kappa a
    by_contra h
    have h_lt : P.kappa a < P.rho a := not_le.mp h
    obtain ⟨q, hq_kappa, hq_rho⟩ := exists_rat_btwn h_lt
    let n := q.num.natAbs
    let m := q.den
    have hm : 0 < m := q.den_pos
    have hq_pos : 0 ≤ q := by
      have h0 : 0 ≤ P.kappa a := by
        apply le_csSup (P.kappa_set_bddAbove a)
        refine ⟨0, 1, Nat.zero_lt_one, ?_, by simp⟩
        simpa using P.zero_le a
      exact Rat.cast_nonneg.mp (h0.trans hq_kappa.le)
    have hq_eq : (q : ℝ) = (n : ℝ) / m := by
      rw [Rat.cast_def]
      field_simp [hm.ne', q.den_pos.ne']
      norm_cast
      have : q.num = (n : ℤ) := (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq_pos)).symm
      rw [this, Int.mul_comm]
      rfl
    have h_rho_imp : P.le (↑m * a) ↑n → False := by
      intro h_le
      have mem : (n : ℝ) / m ∈ P.rho_set a := ⟨n, m, hm, h_le, rfl⟩
      have : P.rho a ≤ (n : ℝ) / m := csInf_le (P.rho_set_bddBelow a) mem
      rw [← hq_eq] at this
      linarith
    have h_kappa_imp : P.le ↑n (↑m * a) → False := by
      intro h_le
      have mem : (n : ℝ) / m ∈ P.kappa_set a := ⟨n, m, hm, h_le, rfl⟩
      have : (n : ℝ) / m ≤ P.kappa a := le_csSup (P.kappa_set_bddAbove a) mem
      rw [← hq_eq] at this
      linarith
    -- Totality contradiction
    cases total (↑m * a) ↑n with
    | inl h_tot => exact h_rho_imp h_tot
    | inr h_tot => exact h_kappa_imp h_tot
  · exact P.kappa_le_rho a

/-! ## `ρ` is additive and multiplicative on a total preorder -/

theorem rho_add (P : StrassenPreorder R) (total : P.IsTotal) (a b : R) :
    P.rho (a + b) = P.rho a + P.rho b := by
  apply le_antisymm
  · exact P.rho_add_le a b
  · rw [P.rho_eq_kappa_of_total total a, P.rho_eq_kappa_of_total total b,
      P.rho_eq_kappa_of_total total (a + b)]
    exact P.kappa_add_ge a b

theorem rho_mul (P : StrassenPreorder R) (total : P.IsTotal) (a b : R) :
    P.rho (a * b) = P.rho a * P.rho b := by
  apply le_antisymm
  · exact P.rho_mul_le a b
  · rw [P.rho_eq_kappa_of_total total a, P.rho_eq_kappa_of_total total b,
      P.rho_eq_kappa_of_total total (a * b)]
    exact P.kappa_mul_ge a b

theorem rho_zero (P : StrassenPreorder R) : P.rho 0 = 0 := by
  rw [← Nat.cast_zero, P.rho_nat_cast]
  simp

theorem rho_one (P : StrassenPreorder R) : P.rho 1 = 1 := by
  rw [← Nat.cast_one, P.rho_nat_cast]
  simp

/-- **The fractional rank as a ring homomorphism for total preorders.**

`ρ : R →+* ℝ` is a semiring homomorphism whenever the Strassen preorder `P` is total. -/
def rho_toRingHom (P : StrassenPreorder R) (total : P.IsTotal) : R →+* ℝ where
  toFun := P.rho
  map_one' := P.rho_one
  map_mul' := P.rho_mul total
  map_zero' := P.rho_zero
  map_add' := P.rho_add total

end StrassenPreorder

end MME


