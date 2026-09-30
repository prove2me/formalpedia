-- Prove2me | solution 1 for linear_neumann_diagonal_centered_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:47:39.036988+00:00
-- url     : https://prove2.me/submissions/3a05c355-ed10-4a1e-b5e9-14530ff2bd9c

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_sampled_counts
import Mathlib
import Definitions.Def_matrix_completion_basic
import Theorems.Thm_centered_sampling_jensen_pointwise_independent_copy_bound_of_sample_ratio
import Mathlib.Tactic
import Theorems.Thm_centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio
import Theorems.Thm_rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio
import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_bernoulli_moment_bound_from_symmetrization_and_auxiliary_moment_bound
import Theorems.Thm_centered_sampling_log_moment_beta_scale_from_khintchine_scale
import Theorems.Thm_rademacher_sampled_matrix_moment_from_row_column_energy_2pN
import Theorems.Thm_fixed_matrix_log_moment_scale_absorbs_markov_failure_factor
import Definitions.Def_matrix_completion_svd
import Theorems.Thm_linear_neumann_diagonal_centered_as_fixed_matrix_fluctuation
import Theorems.Thm_linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
import Theorems.Thm_bernoulli_event_probability_mono

/- Eleven complete accepted-source bodies with explicit import, namespace, and final-name transformations: ReusedSampling.lean; SHA256 6f466c249fb6d68e7d192bbdb648b2e6288faab38a9b949f8b1a5864d31e5831. -/

/- Complete accepted-source reuse: theorem d9cc9674-37b8-41e1-b754-c7b0de571695; submission 871c8194-7a5d-4a6e-ad1e-2514c5e0b009.
Original SHA256 e47e31643f1f9e701cf7323499e87fc9f30166a4df15990ab0c90616401ee719. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_d9cc9674

/-!
# `bernoulli_sampled_row_column_energy_log_moment_bound` (platform node 4337294c)

Self-contained proof using the RELAXED CR2008 Lemma 6.2 (binomial card moment
bounded by `(2x)^q` for any scale `x ≥ n·p` with `q ≤ x`).  Choosing the scale
`x := 2·(n·p)` extends the validity window from `q ≤ n·p` to `q ≤ 2·n·p`, which
is exactly what the one-sample lower bound `m ≥ β·N·log N` (N = max n₁ n₂) can
supply for the exponent `q := ⌈β log N⌉`.

Constant: `C = 8·e`.

All inlined bricks (`CR2008Lemma62`, `Marginal`, `CR2008Lemma62Max`) and the two
energy↔count bridges are reproduced here so the file is self-contained on Mathlib
plus the platform Definitions.
-/

open scoped BigOperators

/-! ## Brick 1 : single-row binomial card moment (relaxed Lemma 6.2) -/

namespace CR2008Lemma62

noncomputable def rowBernoulliMoment (n q : ℕ) (p : ℝ) : ℝ :=
  ∑ S : Finset (Fin n),
    p ^ S.card * (1 - p) ^ (n - S.card) * (S.card : ℝ) ^ q

noncomputable def binomCardMoment (n q : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    ((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k) * (k : ℝ) ^ q

lemma rowBernoulliMoment_eq_binomCardMoment (n q : ℕ) (p : ℝ) :
    rowBernoulliMoment n q p = binomCardMoment n q p := by
  classical
  unfold rowBernoulliMoment binomCardMoment
  let U : Finset (Fin n) := Finset.univ
  have hUcard : U.card = n := by simp [U]
  have h_univ :
      (Finset.univ : Finset (Finset (Fin n))) = U.powerset := by
    ext S
    simp [U]
  rw [h_univ, Finset.sum_powerset, hUcard]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hconst : ∀ t ∈ Finset.powersetCard k U,
      p ^ t.card * (1 - p) ^ (n - t.card) * (t.card : ℝ) ^ q
        = p ^ k * (1 - p) ^ (n - k) * (k : ℝ) ^ q := by
    intro t ht
    rw [(Finset.mem_powersetCard.mp ht).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, hUcard,
      nsmul_eq_mul]
  ring

lemma binomCardMoment_zero (n : ℕ) (p : ℝ) :
    binomCardMoment n 0 p = 1 := by
  unfold binomCardMoment
  have h := add_pow p (1 - p) n
  have hsum :
      (∑ k ∈ Finset.range (n + 1),
        p ^ k * (1 - p) ^ (n - k) * ((n.choose k : ℕ) : ℝ)) = 1 := by
    calc
      (∑ k ∈ Finset.range (n + 1),
        p ^ k * (1 - p) ^ (n - k) * ((n.choose k : ℕ) : ℝ))
          = (p + (1 - p)) ^ n := by
              simpa [mul_assoc, mul_comm, mul_left_comm] using h.symm
      _ = 1 := by ring
  simpa [mul_assoc, mul_comm, mul_left_comm] using hsum

lemma binomCardMoment_nonneg {n q : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binomCardMoment n q p := by
  unfold binomCardMoment
  refine Finset.sum_nonneg ?_
  intro k hk
  have h1mp : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
      (pow_nonneg h1mp _))
    (pow_nonneg (Nat.cast_nonneg _) _)

lemma one_add_two_mul_pow_le_two_mul_pow {q : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) (hxq : (q : ℝ) ≤ x) :
    (1 + 2 * x) ^ q ≤ 2 * (2 * x) ^ q := by
  have hx2 : 0 ≤ 2 * x := by positivity
  have hterm :
      ∀ i ∈ Finset.range (q + 1),
        1 ^ i * (2 * x) ^ (q - i) * ((q.choose i : ℕ) : ℝ)
          ≤ (2 * x) ^ q * ((1 / 2 : ℝ) ^ i) := by
    intro i hi
    have hiq : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hchoose_nat : q.choose i ≤ q ^ i := Nat.choose_le_pow q i
    have hchoose : (((q.choose i : ℕ) : ℝ)) ≤ (x : ℝ) ^ i := by
      calc
        (((q.choose i : ℕ) : ℝ)) ≤ (q : ℝ) ^ i := by
          exact_mod_cast hchoose_nat
        _ ≤ x ^ i := pow_le_pow_left₀ (Nat.cast_nonneg q) hxq i
    have hpow :
        x ^ i * (2 * x) ^ (q - i) = (2 * x) ^ q * ((1 / 2 : ℝ) ^ i) := by
      have hhalf : (2 * x) ^ i * ((1 / 2 : ℝ) ^ i) = x ^ i := by
        rw [← mul_pow]
        ring_nf
      calc
        x ^ i * (2 * x) ^ (q - i)
            = ((2 * x) ^ i * ((1 / 2 : ℝ) ^ i)) * (2 * x) ^ (q - i) := by
                rw [hhalf]
        _ = ((2 * x) ^ i * (2 * x) ^ (q - i)) * ((1 / 2 : ℝ) ^ i) := by
                ring
        _ = (2 * x) ^ q * ((1 / 2 : ℝ) ^ i) := by
                rw [← pow_add, Nat.add_sub_of_le hiq]
    calc
      1 ^ i * (2 * x) ^ (q - i) * (((q.choose i : ℕ) : ℝ))
          = (((q.choose i : ℕ) : ℝ)) * (2 * x) ^ (q - i) := by ring
      _ ≤ x ^ i * (2 * x) ^ (q - i) := by
        exact mul_le_mul_of_nonneg_right hchoose (pow_nonneg hx2 _)
      _ = (2 * x) ^ q * ((1 / 2 : ℝ) ^ i) := hpow
  calc
    (1 + 2 * x) ^ q
        = ∑ i ∈ Finset.range (q + 1),
            1 ^ i * (2 * x) ^ (q - i) * ((q.choose i : ℕ) : ℝ) := by
              simpa [mul_assoc, mul_comm, mul_left_comm] using add_pow (1 : ℝ) (2 * x) q
    _ ≤ ∑ i ∈ Finset.range (q + 1), (2 * x) ^ q * ((1 / 2 : ℝ) ^ i) :=
        Finset.sum_le_sum hterm
    _ = (2 * x) ^ q * (∑ i ∈ Finset.range (q + 1), ((1 / 2 : ℝ) ^ i)) := by
        exact (Finset.mul_sum (Finset.range (q+1)) (fun i => ((1/2:ℝ)^i)) ((2*x)^q)).symm
    _ ≤ (2 * x) ^ q * 2 := by
      have hgeom :
          (∑ i ∈ Finset.range (q + 1), ((1 / 2 : ℝ) ^ i)) ≤ 2 := by
        have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ (q + 1) := by positivity
        rw [geom_sum_eq (show (1 / 2 : ℝ) ≠ 1 by norm_num)]
        rw [div_le_iff_of_neg (by norm_num)]
        nlinarith [hpow_nonneg]
      exact mul_le_mul_of_nonneg_left hgeom (pow_nonneg hx2 _)
    _ = 2 * (2 * x) ^ q := by ring

lemma binomCardMoment_succ_eq (n q : ℕ) (p : ℝ) :
    binomCardMoment (n + 1) (q + 1) p =
      ((n + 1 : ℕ) : ℝ) * p *
        (∑ r ∈ Finset.range (q + 1),
          (((q.choose r : ℕ) : ℝ) * binomCardMoment n r p)) := by
  unfold binomCardMoment
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero q), mul_zero, add_zero]
  have hshift :
      (∑ k ∈ Finset.range (n + 1),
          (((n + 1).choose (k + 1) : ℕ) : ℝ) *
            p ^ (k + 1) * (1 - p) ^ (n + 1 - (k + 1)) *
              ((k + 1 : ℕ) : ℝ) ^ (q + 1))
        =
      ((n + 1 : ℕ) : ℝ) * p *
        (∑ k ∈ Finset.range (n + 1),
          (((n.choose k : ℕ) : ℝ) *
            p ^ k * (1 - p) ^ (n - k) * (((k : ℕ) : ℝ) + 1) ^ q)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : n + 1 - (k + 1) = n - k := Nat.succ_sub_succ_eq_sub n k
    have hchoose :
        (((n + 1).choose (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) =
          ((n + 1 : ℕ) : ℝ) * (((n.choose k : ℕ) : ℝ)) := by
      have hnat := Nat.add_one_mul_choose_eq n k
      exact_mod_cast hnat.symm
    calc
      (((n + 1).choose (k + 1) : ℕ) : ℝ) *
            p ^ (k + 1) * (1 - p) ^ (n + 1 - (k + 1)) *
              ((k + 1 : ℕ) : ℝ) ^ (q + 1)
          = (((n + 1).choose (k + 1) : ℕ) : ℝ) *
              ((k + 1 : ℕ) : ℝ) *
              p * p ^ k * (1 - p) ^ (n - k) *
              (((k : ℕ) : ℝ) + 1) ^ q := by
              rw [hsub, pow_succ' p k, pow_succ]
              norm_num
              ring
      _ = (((n + 1 : ℕ) : ℝ) * (((n.choose k : ℕ) : ℝ))) *
              p * p ^ k * (1 - p) ^ (n - k) *
              (((k : ℕ) : ℝ) + 1) ^ q := by rw [hchoose]
      _ = ((n + 1 : ℕ) : ℝ) * p *
            ((((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k) *
              (((k : ℕ) : ℝ) + 1) ^ q)) := by ring
  have hswap :
      (∑ k ∈ Finset.range (n + 1),
          (((n.choose k : ℕ) : ℝ) *
            p ^ k * (1 - p) ^ (n - k) * (((k : ℕ) : ℝ) + 1) ^ q))
        =
      ∑ r ∈ Finset.range (q + 1),
        (((q.choose r : ℕ) : ℝ) *
          ∑ k ∈ Finset.range (n + 1),
            (((n.choose k : ℕ) : ℝ) *
              p ^ k * (1 - p) ^ (n - k) * (k : ℝ) ^ r)) := by
    have hexpand : ∀ k : ℕ, (((k : ℕ) : ℝ) + 1) ^ q
        = ∑ r ∈ Finset.range (q + 1), (k : ℝ) ^ r * ((q.choose r : ℕ) : ℝ) := by
      intro k
      have := add_pow ((k : ℝ)) (1 : ℝ) q
      simpa [one_pow, mul_one] using this
    calc
      (∑ k ∈ Finset.range (n + 1),
          (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k) * (((k : ℕ) : ℝ) + 1) ^ q))
          = ∑ k ∈ Finset.range (n + 1),
              ∑ r ∈ Finset.range (q + 1),
                (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k)
                  * ((k : ℝ) ^ r * ((q.choose r : ℕ) : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [hexpand k, Finset.mul_sum]
      _ = ∑ r ∈ Finset.range (q + 1),
            ∑ k ∈ Finset.range (n + 1),
                (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k)
                  * ((k : ℝ) ^ r * ((q.choose r : ℕ) : ℝ))) := Finset.sum_comm
      _ = ∑ r ∈ Finset.range (q + 1),
            (((q.choose r : ℕ) : ℝ) *
              ∑ k ∈ Finset.range (n + 1),
                (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k) * (k : ℝ) ^ r)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            rw [Finset.mul_sum (Finset.range (n + 1))
              (fun k =>
                (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k) * (k : ℝ) ^ r))
              (((q.choose r : ℕ) : ℝ))]
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
  rw [hshift, hswap]

theorem binomCardMoment_le_two_mul_scale_pow
    (n q : ℕ) (p x : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hx1 : 1 ≤ x) (hnpx : (n : ℝ) * p ≤ x) (hqx : (q : ℝ) ≤ x) :
    binomCardMoment n q p ≤ (2 * x) ^ q := by
  revert n x
  refine Nat.strong_induction_on q ?_
  intro q ih n x hx1 hnpx hqx
  cases q with
  | zero =>
      simp [binomCardMoment_zero]
  | succ q =>
      cases n with
      | zero =>
          have hx0 : 0 ≤ x := le_trans zero_le_one hx1
          unfold binomCardMoment
          simp [pow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx0)]
      | succ n =>
          have hx0 : 0 ≤ x := le_trans zero_le_one hx1
          have hq_le_x : (q : ℝ) ≤ x := by
            exact (Nat.cast_le.mpr (Nat.le_succ q)).trans hqx
          have hscale_n : (n : ℝ) * p ≤ x := by
            have hnle : (n : ℝ) ≤ (n + 1 : ℕ) := by norm_num
            have hp0' : 0 ≤ p := hp0
            calc
              (n : ℝ) * p ≤ ((n + 1 : ℕ) : ℝ) * p :=
                mul_le_mul_of_nonneg_right hnle hp0'
              _ ≤ x := hnpx
          have hsum_nonneg :
              0 ≤ ∑ r ∈ Finset.range (q + 1),
                (((q.choose r : ℕ) : ℝ) * binomCardMoment n r p) := by
            refine Finset.sum_nonneg ?_
            intro r hr
            exact mul_nonneg (Nat.cast_nonneg _)
              (binomCardMoment_nonneg (n := n) (q := r) hp0 hp1)
          have hsum_le :
              (∑ r ∈ Finset.range (q + 1),
                (((q.choose r : ℕ) : ℝ) * binomCardMoment n r p))
                ≤ ∑ r ∈ Finset.range (q + 1),
                    (((q.choose r : ℕ) : ℝ) * (2 * x) ^ r) := by
            refine Finset.sum_le_sum ?_
            intro r hr
            have hrq : r ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
            have hrx : (r : ℝ) ≤ x := by
              exact (Nat.cast_le.mpr hrq).trans hq_le_x
            have hrlt : r < q + 1 := Finset.mem_range.mp hr
            have hrec := ih r hrlt n x hx1 hscale_n hrx
            exact mul_le_mul_of_nonneg_left hrec (by positivity)
          have hsum_eval :
              (∑ r ∈ Finset.range (q + 1),
                    (((q.choose r : ℕ) : ℝ) * (2 * x) ^ r))
                = (1 + 2 * x) ^ q := by
            simpa [mul_assoc, mul_comm, mul_left_comm, add_comm] using
              (add_pow (2 * x) (1 : ℝ) q).symm
          calc
            binomCardMoment (n + 1) (q + 1) p
                = ((n + 1 : ℕ) : ℝ) * p *
                    (∑ r ∈ Finset.range (q + 1),
                      (((q.choose r : ℕ) : ℝ) * binomCardMoment n r p)) := by
                    rw [binomCardMoment_succ_eq]
            _ ≤ x *
                    (∑ r ∈ Finset.range (q + 1),
                      (((q.choose r : ℕ) : ℝ) * binomCardMoment n r p)) := by
                    exact mul_le_mul_of_nonneg_right hnpx hsum_nonneg
            _ ≤ x *
                    (∑ r ∈ Finset.range (q + 1),
                      (((q.choose r : ℕ) : ℝ) * (2 * x) ^ r)) := by
                    exact mul_le_mul_of_nonneg_left hsum_le hx0
            _ = x * (1 + 2 * x) ^ q := by rw [hsum_eval]
            _ ≤ x * (2 * (2 * x) ^ q) := by
                    exact mul_le_mul_of_nonneg_left
                      (one_add_two_mul_pow_le_two_mul_pow hx0 hq_le_x) hx0
            _ = (2 * x) ^ (q + 1) := by ring

/-- Relaxed Lemma 6.2 with scale `x := 2·(n·p)`: valid up to `q ≤ 2·n·p`. -/
theorem rowBernoulliMoment_le_four_np_pow
    (n q : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq2np : (q : ℝ) ≤ 2 * ((n : ℝ) * p))
    (h1 : 1 ≤ 2 * ((n : ℝ) * p)) :
    rowBernoulliMoment n q p ≤ (4 * ((n : ℝ) * p)) ^ q := by
  rw [rowBernoulliMoment_eq_binomCardMoment]
  have hx1 : 1 ≤ 2 * ((n : ℝ) * p) := h1
  have hnpx : (n : ℝ) * p ≤ 2 * ((n : ℝ) * p) := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hp0]
  have := binomCardMoment_le_two_mul_scale_pow n q p (2 * ((n : ℝ) * p)) hp0 hp1 hx1 hnpx hq2np
  calc binomCardMoment n q p ≤ (2 * (2 * ((n : ℝ) * p))) ^ q := this
    _ = (4 * ((n : ℝ) * p)) ^ q := by ring_nf

end CR2008Lemma62

/-! ## Brick 2 : marginalization (single-row q-moment) -/

namespace Marginal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weight_eq_prod (p : ℝ) (Omega : Finset ι) :
    p ^ Omega.card * (1 - p) ^ (Fintype.card ι - Omega.card)
      = ∏ c : ι, (if c ∈ Omega then p else (1 - p)) := by
  classical
  have hsplit :
      (∏ c : ι, (if c ∈ Omega then p else (1 - p)))
        = (∏ c ∈ Omega, p) * (∏ c ∈ (Finset.univ \ Omega), (1 - p)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun c => c ∈ Omega)]
    congr 1
    · apply Finset.prod_congr
      · ext c; simp
      · intro c hc; simp at hc; simp [hc]
    · apply Finset.prod_congr
      · ext c; simp
      · intro c hc; simp at hc; simp [hc]
  rw [hsplit]
  rw [Finset.prod_const, Finset.prod_const]
  have hc : (Finset.univ \ Omega).card = Fintype.card ι - Omega.card := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
  rw [hc]

lemma sum_powerset_split (A : Finset ι) (F : Finset ι → ℝ) :
    (∑ Omega : Finset ι, F Omega)
      = ∑ Sa ∈ A.powerset, ∑ Sr ∈ Aᶜ.powerset, F (Sa ∪ Sr) := by
  classical
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij' (i := fun Omega => ⟨Omega ∩ A, Omega ∩ Aᶜ⟩)
    (j := fun x => x.1 ∪ x.2)
  · intro Omega _
    simp only [Finset.mem_sigma, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro x hx
    exact Finset.mem_univ _
  · intro Omega _
    rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hx
    obtain ⟨hSa, hSr⟩ := hx
    have hSadisj : Disjoint x.1 Aᶜ := Disjoint.mono_left hSa disjoint_compl_right
    have hSrdisj : Disjoint x.2 A := Disjoint.mono_left hSr disjoint_compl_left
    ext
    · simp only [Finset.union_inter_distrib_right]
      rw [Finset.inter_eq_left.mpr hSa, (Finset.disjoint_iff_inter_eq_empty.mp hSrdisj)]
      simp
    · simp only [Finset.union_inter_distrib_right]
      rw [Finset.inter_eq_left.mpr hSr, (Finset.disjoint_iff_inter_eq_empty.mp hSadisj)]
      simp
  · intro Omega _
    congr 1
    rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]

lemma rest_sum_one (p : ℝ) (B : Finset ι) :
    (∑ Sr ∈ B.powerset, ∏ c ∈ B, (if c ∈ Sr then p else (1 - p))) = 1 := by
  classical
  have key : ∀ Sr ∈ B.powerset,
      (∏ c ∈ B, (if c ∈ Sr then p else (1 - p)))
        = (∏ c ∈ Sr, p) * ∏ c ∈ B \ Sr, (1 - p) := by
    intro Sr hSr
    rw [Finset.mem_powerset] at hSr
    classical
    rw [← Finset.prod_filter_mul_prod_filter_not B (fun c => c ∈ Sr)]
    congr 1
    · refine Finset.prod_congr ?_ (fun c hc => ?_)
      · ext c; simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hSr h, h⟩⟩
      · rw [if_pos hc]
    · refine Finset.prod_congr ?_ (fun c hc => ?_)
      · ext c; simp only [Finset.mem_filter, Finset.mem_sdiff, and_comm]
      · rw [Finset.mem_sdiff] at hc; rw [if_neg hc.2]
  rw [Finset.sum_congr rfl key]
  rw [← Finset.prod_add]
  apply Finset.prod_eq_one
  intro c _; ring

noncomputable def rowCount {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (a : Fin n1) : ℕ :=
  (Finset.univ.filter (fun b : Fin n2 => (a, b) ∈ Omega)).card

noncomputable def bExp2 {n1 n2 : ℕ} (p : ℝ) (F : Finset (Fin n1 × Fin n2) → ℝ) : ℝ :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card) * F Omega

noncomputable def rowBern (n q : ℕ) (p : ℝ) : ℝ :=
  ∑ S : Finset (Fin n), p ^ S.card * (1 - p) ^ (n - S.card) * (S.card : ℝ) ^ q

def rowCells {n1 n2 : ℕ} (a : Fin n1) : Finset (Fin n1 × Fin n2) :=
  Finset.univ.filter (fun c => c.1 = a)

lemma rowCount_union {n1 n2 : ℕ} (a : Fin n1)
    {Sa Sr : Finset (Fin n1 × Fin n2)} (hSa : Sa ⊆ rowCells a) (hSr : Sr ⊆ (rowCells a)ᶜ) :
    rowCount (Sa ∪ Sr) a = Sa.card := by
  classical
  unfold rowCount
  refine Finset.card_nbij' (i := fun b : Fin n2 => ((a, b) : Fin n1 × Fin n2))
    (j := fun c : Fin n1 × Fin n2 => c.2) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_coe, Finset.mem_filter] at hb
    rw [Finset.mem_coe]
    rcases Finset.mem_union.mp hb.2 with hb' | hb'
    · exact hb'
    · exfalso
      have hmem := hSr hb'
      rw [Finset.mem_compl, rowCells, Finset.mem_filter] at hmem
      exact hmem ⟨Finset.mem_univ _, rfl⟩
  · intro c hc
    rw [Finset.mem_coe] at hc
    have hc1 : c.1 = a := by
      have := hSa hc
      simp only [rowCells, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_union.mpr; left
    have : (a, c.2) = c := by rw [← hc1]
    rw [this]; exact hc
  · intro b _; rfl
  · intro c hc
    rw [Finset.mem_coe] at hc
    have hc1 : c.1 = a := by
      have := hSa hc
      simp only [rowCells, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    show (a, c.2) = c
    rw [← hc1]

lemma card_rowCells {n1 n2 : ℕ} (a : Fin n1) :
    (rowCells (n2 := n2) a).card = n2 := by
  classical
  have : (rowCells (n2 := n2) a).card = (Finset.univ : Finset (Fin n2)).card := by
    apply Finset.card_nbij' (i := fun c : Fin n1 × Fin n2 => c.2)
      (j := fun b : Fin n2 => ((a, b) : Fin n1 × Fin n2))
    · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro b _
      rw [Finset.mem_coe, rowCells, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, rfl⟩
    · intro c hc
      rw [Finset.mem_coe, rowCells, Finset.mem_filter] at hc
      show (a, c.2) = c
      rw [← hc.2]
    · intro b _; rfl
  rw [this, Finset.card_univ, Fintype.card_fin]

lemma snd_pair_inj {n1 n2 : ℕ} (a : Fin n1) :
    Function.Injective (fun b : Fin n2 => ((a, b) : Fin n1 × Fin n2)) := by
  intro b1 b2 h; simpa using h

lemma image_pair_card {n1 n2 : ℕ} (a : Fin n1) (S : Finset (Fin n2)) :
    (S.image (fun b => ((a, b) : Fin n1 × Fin n2))).card = S.card :=
  Finset.card_image_of_injective S (snd_pair_inj a)

lemma prod_rowCells_image {n1 n2 : ℕ} (p : ℝ) (a : Fin n1) (S : Finset (Fin n2)) :
    (∏ c ∈ rowCells (n2 := n2) a,
        (if c ∈ S.image (fun b => ((a, b) : Fin n1 × Fin n2)) then p else (1 - p)))
      = p ^ S.card * (1 - p) ^ (n2 - S.card) := by
  classical
  rw [show (∏ c ∈ rowCells (n2 := n2) a,
        (if c ∈ S.image (fun b => ((a, b) : Fin n1 × Fin n2)) then p else (1 - p)))
        = ∏ b : Fin n2, (if b ∈ S then p else (1 - p)) from ?_]
  · have := weight_eq_prod (ι := Fin n2) p S
    rw [Fintype.card_fin] at this
    exact this.symm
  · apply Finset.prod_nbij' (i := fun c : Fin n1 × Fin n2 => c.2)
      (j := fun b : Fin n2 => ((a, b) : Fin n1 × Fin n2))
    · intro c _; exact Finset.mem_univ _
    · intro b _
      rw [rowCells, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩
    · intro c hc
      rw [rowCells, Finset.mem_filter] at hc
      show (a, c.2) = c; rw [← hc.2]
    · intro b _; rfl
    · intro c hc
      rw [rowCells, Finset.mem_filter] at hc
      congr 1
      apply propext
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨b, hb, hbc⟩
        have : b = c.2 := by rw [← hbc]
        rw [← this]; exact hb
      · intro hc2
        exact ⟨c.2, hc2, by show (a, c.2) = c; rw [← hc.2]⟩

theorem bExp2_rowCount_pow_eq_rowBern {n1 n2 : ℕ} (p : ℝ) (a : Fin n1) (q : ℕ) :
    bExp2 (n1 := n1) (n2 := n2) p (fun Omega => (rowCount Omega a : ℝ) ^ q) = rowBern n2 q p := by
  classical
  unfold bExp2
  have hstep1 : ∀ Omega : Finset (Fin n1 × Fin n2),
      p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card)
          * (rowCount Omega a : ℝ) ^ q
        = (∏ c : Fin n1 × Fin n2, (if c ∈ Omega then p else (1 - p))) * (rowCount Omega a : ℝ) ^ q := by
    intro Omega; rw [weight_eq_prod]
  rw [Finset.sum_congr rfl (fun Omega _ => hstep1 Omega)]
  rw [sum_powerset_split (rowCells a)
      (fun Omega => (∏ c : Fin n1 × Fin n2, (if c ∈ Omega then p else (1 - p)))
        * (rowCount Omega a : ℝ) ^ q)]
  have hinner : ∀ Sa ∈ (rowCells a).powerset, ∀ Sr ∈ (rowCells a)ᶜ.powerset,
      (∏ c : Fin n1 × Fin n2, (if c ∈ (Sa ∪ Sr) then p else (1 - p)))
          * (rowCount (Sa ∪ Sr) a : ℝ) ^ q
        = ((∏ c ∈ rowCells a, (if c ∈ Sa then p else (1 - p))) * (Sa.card : ℝ) ^ q)
            * (∏ c ∈ (rowCells a)ᶜ, (if c ∈ Sr then p else (1 - p))) := by
    intro Sa hSa Sr hSr
    rw [Finset.mem_powerset] at hSa hSr
    have hsplitprod :
        (∏ c : Fin n1 × Fin n2, (if c ∈ (Sa ∪ Sr) then p else (1 - p)))
          = (∏ c ∈ rowCells a, (if c ∈ (Sa ∪ Sr) then p else (1 - p)))
            * (∏ c ∈ (rowCells a)ᶜ, (if c ∈ (Sa ∪ Sr) then p else (1 - p))) := by
      rw [← Finset.prod_mul_prod_compl (rowCells a)
            (fun c => (if c ∈ (Sa ∪ Sr) then p else (1 - p)))]
    rw [hsplitprod, rowCount_union a hSa hSr]
    have hOnRow : (∏ c ∈ rowCells a, (if c ∈ (Sa ∪ Sr) then p else (1 - p)))
        = (∏ c ∈ rowCells a, (if c ∈ Sa then p else (1 - p))) := by
      refine Finset.prod_congr rfl (fun c hc => ?_)
      have hcsr : c ∉ Sr := fun h => (Finset.mem_compl.mp (hSr h)) hc
      by_cases hcsa : c ∈ Sa
      · rw [if_pos (Finset.mem_union.mpr (Or.inl hcsa)), if_pos hcsa]
      · rw [if_neg (by simp [Finset.mem_union, hcsa, hcsr]), if_neg hcsa]
    have hOnComp : (∏ c ∈ (rowCells a)ᶜ, (if c ∈ (Sa ∪ Sr) then p else (1 - p)))
        = (∏ c ∈ (rowCells a)ᶜ, (if c ∈ Sr then p else (1 - p))) := by
      refine Finset.prod_congr rfl (fun c hc => ?_)
      have hcsa : c ∉ Sa := fun h => (Finset.mem_compl.mp hc) (hSa h)
      by_cases hcsr : c ∈ Sr
      · rw [if_pos (Finset.mem_union.mpr (Or.inr hcsr)), if_pos hcsr]
      · rw [if_neg (by simp [Finset.mem_union, hcsa, hcsr]), if_neg hcsr]
    rw [hOnRow, hOnComp]; ring
  rw [Finset.sum_congr rfl (fun Sa hSa => Finset.sum_congr rfl (fun Sr hSr => hinner Sa hSa Sr hSr))]
  have hfactor : ∀ Sa ∈ (rowCells (n2 := n2) a).powerset,
      (∑ Sr ∈ (rowCells (n2 := n2) a)ᶜ.powerset,
        ((∏ c ∈ rowCells (n2 := n2) a, (if c ∈ Sa then p else (1 - p))) * (Sa.card : ℝ) ^ q)
          * (∏ c ∈ (rowCells (n2 := n2) a)ᶜ, (if c ∈ Sr then p else (1 - p))))
        = (∏ c ∈ rowCells (n2 := n2) a, (if c ∈ Sa then p else (1 - p))) * (Sa.card : ℝ) ^ q := by
    intro Sa _
    have hrest := rest_sum_one (ι := Fin n1 × Fin n2) p ((rowCells a)ᶜ)
    rw [← Finset.mul_sum, hrest, mul_one]
  rw [Finset.sum_congr rfl hfactor]
  unfold rowBern
  refine (Finset.sum_nbij' (i := fun S : Finset (Fin n2) => S.image (fun b => ((a, b) : Fin n1 × Fin n2)))
    (j := fun Sa : Finset (Fin n1 × Fin n2) => Sa.image (fun c => c.2)) ?_ ?_ ?_ ?_ ?_).symm
  · intro S hS
    rw [Finset.mem_powerset]
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨b, _, hbc⟩ := hc
    rw [rowCells, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [← hbc]⟩
  · intro Sa _; exact Finset.mem_univ _
  · intro S _
    dsimp only
    rw [Finset.image_image]
    simp
  · intro Sa hSa
    rw [Finset.mem_powerset] at hSa
    dsimp only
    rw [Finset.image_image]
    rw [Finset.image_congr (g := fun c : Fin n1 × Fin n2 => c) ?_, Finset.image_id']
    intro c hc
    have := hSa hc
    rw [rowCells, Finset.mem_filter] at this
    show (a, c.2) = c; rw [← this.2]
  · intro S _
    rw [prod_rowCells_image p a S, image_pair_card a S]

end Marginal

/-! ## Brick 3 : max-over-rows moment -/

namespace CR2008Lemma62Max

noncomputable def rowCount {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (a : Fin n1) : ℕ :=
  (Finset.univ.filter (fun b : Fin n2 => (a, b) ∈ Omega)).card

noncomputable def bExp {n1 n2 : ℕ} (p : ℝ) (F : Finset (Fin n1 × Fin n2) → ℝ) : ℝ :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card) * F Omega

lemma max_pow_le_sum_pow {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (q : ℕ) :
    (⨆ i, f i) ^ q ≤ ∑ i, (f i) ^ q := by
  classical
  obtain ⟨a, ha⟩ := Finite.exists_max f
  have hsup : (⨆ i, f i) = f a := by
    apply le_antisymm
    · apply ciSup_le; intro i; exact ha i
    · exact le_ciSup (Finite.bddAbove_range f) a
  rw [hsup]
  calc (f a) ^ q ≤ ∑ i, (f i) ^ q := by
        refine Finset.single_le_sum (f := fun i => (f i) ^ q) ?_ (Finset.mem_univ a)
        intro i _; exact pow_nonneg (hf i) q

lemma bExp_sum {n1 n2 : ℕ} (p : ℝ) {κ : Type*} (s : Finset κ)
    (F : κ → Finset (Fin n1 × Fin n2) → ℝ) :
    bExp p (fun Omega => ∑ a ∈ s, F a Omega) = ∑ a ∈ s, bExp p (fun Omega => F a Omega) := by
  classical
  unfold bExp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Omega _
  rw [Finset.mul_sum]

lemma bExp_mono {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : Finset (Fin n1 × Fin n2) → ℝ} (h : ∀ Omega, F Omega ≤ G Omega) :
    bExp p F ≤ bExp p G := by
  classical
  unfold bExp
  apply Finset.sum_le_sum
  intro Omega _
  have hw : 0 ≤ p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card) := by
    apply mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_left (h Omega) hw

lemma bExp_add {n1 n2 : ℕ} (p : ℝ) (F G : Finset (Fin n1 × Fin n2) → ℝ) :
    bExp p (fun Omega => F Omega + G Omega) = bExp p F + bExp p G := by
  unfold bExp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Omega _; ring

lemma bExp_smul {n1 n2 : ℕ} (p c : ℝ) (F : Finset (Fin n1 × Fin n2) → ℝ) :
    bExp p (fun Omega => c * F Omega) = c * bExp p F := by
  unfold bExp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Omega _; ring

theorem bExp_max_rowCount_pow_le {n1 n2 : ℕ} [Nonempty (Fin n1)] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ)
    (B : ℝ)
    (hrow : ∀ a : Fin n1,
      bExp p (fun Omega : Finset (Fin n1 × Fin n2) => (rowCount Omega a : ℝ) ^ q) ≤ B) :
    bExp p (fun Omega : Finset (Fin n1 × Fin n2) => (⨆ a : Fin n1, (rowCount Omega a : ℝ)) ^ q)
      ≤ (n1 : ℝ) * B := by
  classical
  have hpt : ∀ Omega : Finset (Fin n1 × Fin n2),
      (⨆ a : Fin n1, (rowCount Omega a : ℝ)) ^ q
        ≤ ∑ a : Fin n1, ((rowCount Omega a : ℝ)) ^ q :=
    fun Omega => max_pow_le_sum_pow (fun a => (rowCount Omega a : ℝ)) (fun a => by positivity) q
  calc bExp p (fun Omega : Finset (Fin n1 × Fin n2) => (⨆ a : Fin n1, (rowCount Omega a : ℝ)) ^ q)
      ≤ bExp p (fun Omega : Finset (Fin n1 × Fin n2) => ∑ a : Fin n1, ((rowCount Omega a : ℝ)) ^ q) :=
        bExp_mono hp0 hp1 hpt
    _ = ∑ a : Fin n1, bExp p (fun Omega : Finset (Fin n1 × Fin n2) => ((rowCount Omega a : ℝ)) ^ q) :=
        bExp_sum (n1 := n1) (n2 := n2) p Finset.univ
          (fun a Omega => ((rowCount Omega a : ℝ)) ^ q)
    _ ≤ ∑ _a : Fin n1, B := Finset.sum_le_sum (fun a _ => hrow a)
    _ = (n1 : ℝ) * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end CR2008Lemma62Max

/-! ## Assembly -/

namespace Sol2pNctrl

open MatrixCompletion
open scoped Classical BigOperators

/-- The platform `bernoulliExpectation` is the inlined `bExp`. -/
lemma bernoulliExpectation_eq_bExp {n1 n2 : ℕ} (p : ℝ)
    (F : Finset (Fin n1 × Fin n2) → ℝ) :
    bernoulliExpectation p F = CR2008Lemma62Max.bExp p F := by
  unfold bernoulliExpectation CR2008Lemma62Max.bExp bernoulliObservationWeight
  rfl

/-- `∑_j 1[(i,j)∈Ω]` equals the `rowCount`. -/
lemma sum_indicator_eq_rowCount {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) (i : Fin n1) :
    (∑ j : Fin n2, if (i, j) ∈ Omega then (1 : ℝ) else 0)
      = (CR2008Lemma62Max.rowCount Omega i : ℝ) := by
  classical
  unfold CR2008Lemma62Max.rowCount
  rw [Finset.sum_boole]

/-- `sampledRowCountMax` equals `⨆ i, rowCount`. -/
lemma sampledRowCountMax_eq_iSup {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) :
    sampledRowCountMax Omega
      = ⨆ i : Fin n1, (CR2008Lemma62Max.rowCount Omega i : ℝ) := by
  unfold sampledRowCountMax
  congr 1
  ext i
  exact sum_indicator_eq_rowCount Omega i

/-- Inlined row energy↔count bridge. -/
lemma sampledRowEnergyMax_le {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) (X : Matrix (Fin n1) (Fin n2) ℝ) :
    sampledRowEnergyMax Omega X ≤ entrySupNorm X ^ 2 * sampledRowCountMax Omega := by
  by_cases h₁ : IsEmpty (Fin n1)
  · haveI := h₁
    simp [sampledRowEnergyMax, sampledRowCountMax]
  · by_cases h₂ : IsEmpty (Fin n2)
    · haveI := h₂
      simp [sampledRowEnergyMax, sampledRowCountMax]
    · have hn₁ : Nonempty (Fin n1) := not_isEmpty_iff.mp h₁
      have hn₂ : Nonempty (Fin n2) := not_isEmpty_iff.mp h₂
      have hentry_nonneg : 0 ≤ entrySupNorm X := by
        rcases hn₁ with ⟨i0⟩
        rcases hn₂ with ⟨j0⟩
        exact le_trans (abs_nonneg (X i0 j0))
          (le_trans
            (le_ciSup (Finite.bddAbove_range (fun j : Fin n2 => |X i0 j|)) j0)
            (le_ciSup
              (Finite.bddAbove_range (fun i : Fin n1 => ⨆ j : Fin n2, |X i j|)) i0))
      unfold sampledRowEnergyMax
      apply ciSup_le
      intro i
      unfold sampledRowCountMax
      have hrow :
          (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0) ≤
            entrySupNorm X ^ 2 *
              (∑ j : Fin n2, if (i, j) ∈ Omega then (1 : ℝ) else 0) := by
        calc
          (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)
              ≤ ∑ j : Fin n2, if (i, j) ∈ Omega then entrySupNorm X ^ 2 else 0 := by
                apply Finset.sum_le_sum
                intro j _hj
                by_cases hmem : (i, j) ∈ Omega
                · simp [hmem]
                  have hij_abs : |X i j| ≤ entrySupNorm X := by
                    exact le_trans
                      (le_ciSup (Finite.bddAbove_range (fun j : Fin n2 => |X i j|)) j)
                      (le_ciSup
                        (Finite.bddAbove_range
                          (fun i : Fin n1 => ⨆ j : Fin n2, |X i j|)) i)
                  rw [← sq_abs (X i j)]
                  exact sq_le_sq'
                    (le_trans (neg_nonpos.mpr hentry_nonneg) (abs_nonneg (X i j))) hij_abs
                · simp [hmem]
          _ = entrySupNorm X ^ 2 *
              (∑ j : Fin n2, if (i, j) ∈ Omega then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                by_cases hmem : (i, j) ∈ Omega
                · simp [hmem]
                · simp [hmem]
      exact le_trans hrow
        (mul_le_mul_of_nonneg_left
          (le_ciSup
            (Finite.bddAbove_range
              (fun i : Fin n1 =>
                ∑ j : Fin n2, if (i, j) ∈ Omega then (1 : ℝ) else 0)) i)
          (sq_nonneg (entrySupNorm X)))

/-- Inlined column energy↔count bridge. -/
lemma sampledColumnEnergyMax_le {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) (X : Matrix (Fin n1) (Fin n2) ℝ) :
    sampledColumnEnergyMax Omega X ≤ entrySupNorm X ^ 2 * sampledColumnCountMax Omega := by
  by_cases h₁ : IsEmpty (Fin n1)
  · haveI := h₁
    simp [sampledColumnEnergyMax, sampledColumnCountMax]
  · by_cases h₂ : IsEmpty (Fin n2)
    · haveI := h₂
      simp [sampledColumnEnergyMax, sampledColumnCountMax]
    · have hn₁ : Nonempty (Fin n1) := not_isEmpty_iff.mp h₁
      have hn₂ : Nonempty (Fin n2) := not_isEmpty_iff.mp h₂
      have hentry_nonneg : 0 ≤ entrySupNorm X := by
        rcases hn₁ with ⟨i0⟩
        rcases hn₂ with ⟨j0⟩
        exact le_trans (abs_nonneg (X i0 j0))
          (le_trans
            (le_ciSup (Finite.bddAbove_range (fun j : Fin n2 => |X i0 j|)) j0)
            (le_ciSup
              (Finite.bddAbove_range (fun i : Fin n1 => ⨆ j : Fin n2, |X i j|)) i0))
      unfold sampledColumnEnergyMax
      apply ciSup_le
      intro j
      unfold sampledColumnCountMax
      have hcol :
          (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0) ≤
            entrySupNorm X ^ 2 *
              (∑ i : Fin n1, if (i, j) ∈ Omega then (1 : ℝ) else 0) := by
        calc
          (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)
              ≤ ∑ i : Fin n1, if (i, j) ∈ Omega then entrySupNorm X ^ 2 else 0 := by
                apply Finset.sum_le_sum
                intro i _hi
                by_cases hmem : (i, j) ∈ Omega
                · simp [hmem]
                  have hij_abs : |X i j| ≤ entrySupNorm X := by
                    exact le_trans
                      (le_ciSup (Finite.bddAbove_range (fun j : Fin n2 => |X i j|)) j)
                      (le_ciSup
                        (Finite.bddAbove_range
                          (fun i : Fin n1 => ⨆ j : Fin n2, |X i j|)) i)
                  rw [← sq_abs (X i j)]
                  exact sq_le_sq'
                    (le_trans (neg_nonpos.mpr hentry_nonneg) (abs_nonneg (X i j))) hij_abs
                · simp [hmem]
          _ = entrySupNorm X ^ 2 *
              (∑ i : Fin n1, if (i, j) ∈ Omega then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _hi
                by_cases hmem : (i, j) ∈ Omega
                · simp [hmem]
                · simp [hmem]
      exact le_trans hcol
        (mul_le_mul_of_nonneg_left
          (le_ciSup
            (Finite.bddAbove_range
              (fun j : Fin n2 =>
                ∑ i : Fin n1, if (i, j) ∈ Omega then (1 : ℝ) else 0)) j)
          (sq_nonneg (entrySupNorm X)))

/-! ### Per-row / per-column moment via marginalization + relaxed Lemma 6.2 -/

/-- `Marginal.rowBern` is `CR2008Lemma62.rowBernoulliMoment`. -/
lemma rowBern_eq {n : ℕ} (q : ℕ) (p : ℝ) :
    Marginal.rowBern n q p = CR2008Lemma62.rowBernoulliMoment n q p := rfl

/-- Per-row q-moment of the row count, bounded by the relaxed Lemma 6.2 scale. -/
lemma per_row_bound {n1 n2 : ℕ} (p : ℝ) (a : Fin n1) (q : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq2np : (q : ℝ) ≤ 2 * ((n2 : ℝ) * p))
    (h1 : 1 ≤ 2 * ((n2 : ℝ) * p)) :
    CR2008Lemma62Max.bExp p
        (fun Omega : Finset (Fin n1 × Fin n2) => (CR2008Lemma62Max.rowCount Omega a : ℝ) ^ q)
      ≤ (4 * ((n2 : ℝ) * p)) ^ q := by
  -- bExp = bExp2, rowCount = rowCount, marginalize to rowBern, then relaxed Lemma 6.2
  have hmarg :
      CR2008Lemma62Max.bExp p
        (fun Omega : Finset (Fin n1 × Fin n2) => (CR2008Lemma62Max.rowCount Omega a : ℝ) ^ q)
        = Marginal.rowBern n2 q p := by
    have := Marginal.bExp2_rowCount_pow_eq_rowBern (n1 := n1) (n2 := n2) p a q
    -- bExp2 ≡ bExp, Marginal.rowCount ≡ CR2008Lemma62Max.rowCount  (definitionally)
    exact this
  rw [hmarg, rowBern_eq]
  exact CR2008Lemma62.rowBernoulliMoment_le_four_np_pow n2 q p hp0 hp1 hq2np h1

/-- Column count of `Ω` in column `b`. -/
noncomputable def colCount {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (b : Fin n2) : ℕ :=
  (Finset.univ.filter (fun a : Fin n1 => (a, b) ∈ Omega)).card

/-- Image of an observation set under product swap. -/
noncomputable def swapSet {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) :
    Finset (Fin n2 × Fin n1) :=
  Omega.map (Equiv.prodComm (Fin n1) (Fin n2)).toEmbedding

@[simp] lemma mem_swapSet {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2))
    (c : Fin n2 × Fin n1) : c ∈ swapSet Omega ↔ (c.2, c.1) ∈ Omega := by
  unfold swapSet
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨(c.2, c.1), h, by simp [Equiv.prodComm]⟩

lemma swapSet_card {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) :
    (swapSet Omega).card = Omega.card := by
  unfold swapSet; rw [Finset.card_map]

/-- Column count equals the row count of the swapped set. -/
lemma colCount_eq_rowCount_swap {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) (b : Fin n2) :
    colCount Omega b = CR2008Lemma62Max.rowCount (swapSet Omega) b := by
  unfold colCount CR2008Lemma62Max.rowCount
  congr 1
  apply Finset.filter_congr
  intro a _
  simp [mem_swapSet]

/-- `swapSet` is a bijection on all subsets, so `bExp` of a `colCount` statistic over
`Fin n1 × Fin n2` equals `bExp` of the matching `rowCount` statistic over `Fin n2 × Fin n1`. -/
lemma bExp_colCount_eq_bExp_rowCount {n1 n2 : ℕ} (p : ℝ) (b : Fin n2) (q : ℕ) :
    CR2008Lemma62Max.bExp p
        (fun Omega : Finset (Fin n1 × Fin n2) => (colCount Omega b : ℝ) ^ q)
      = CR2008Lemma62Max.bExp p
        (fun Omega : Finset (Fin n2 × Fin n1) => (CR2008Lemma62Max.rowCount Omega b : ℝ) ^ q) := by
  classical
  unfold CR2008Lemma62Max.bExp
  refine Finset.sum_nbij'
    (i := fun Omega : Finset (Fin n1 × Fin n2) => swapSet Omega)
    (j := fun Omega : Finset (Fin n2 × Fin n1) =>
      Omega.map (Equiv.prodComm (Fin n2) (Fin n1)).toEmbedding)
    (fun Omega _ => Finset.mem_univ _) (fun Omega _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro Omega _
    -- left inverse: map (prodComm n2 n1) (swapSet Omega) = Omega
    unfold swapSet
    ext c
    simp only [Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap]
  · intro Omega _
    -- right inverse
    unfold swapSet
    ext c
    simp only [Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap]
  · intro Omega _
    simp only []
    have hcard : Fintype.card (Fin n1 × Fin n2) = Fintype.card (Fin n2 × Fin n1) := by
      rw [Fintype.card_prod, Fintype.card_prod, Nat.mul_comm]
    rw [hcard, swapSet_card, colCount_eq_rowCount_swap]

/-- Per-column q-moment bound (relaxed Lemma 6.2, swapped dimensions). -/
lemma per_col_bound {n1 n2 : ℕ} (p : ℝ) (b : Fin n2) (q : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq2np : (q : ℝ) ≤ 2 * ((n1 : ℝ) * p))
    (h1 : 1 ≤ 2 * ((n1 : ℝ) * p)) :
    CR2008Lemma62Max.bExp p
        (fun Omega : Finset (Fin n1 × Fin n2) => (colCount Omega b : ℝ) ^ q)
      ≤ (4 * ((n1 : ℝ) * p)) ^ q := by
  rw [bExp_colCount_eq_bExp_rowCount]
  exact per_row_bound (n1 := n2) (n2 := n1) p b q hp0 hp1 hq2np h1

/-! ### Exponent window (the genuine content beyond the bricks) -/

/-- The exponent-window lemma under the ONE-sample lower bound `m ≥ β N log N`,
exploiting the relaxed `q ≤ 2·n·p` validity range.  We take `q = ⌈β log N⌉` (at
least `1`) and certify `q ≤ 2·(n_i·p)` for both `i`, i.e. `q ≤ 2·m/N`. -/
lemma q_window_two_np
    (β : ℝ) (hβ : 2 < β) (n₁ n₂ m : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hm1 : 1 ≤ m)
    (hmLower : (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)))
    (hN2 : 2 ≤ max n₁ n₂) :
    ∃ q : ℕ, 1 ≤ q ∧
      (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
      (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
      (q : ℝ) ≤ 2 * ((m : ℝ) / ((↑(max n₁ n₂) : ℝ))) := by
  set N := max n₁ n₂ with hN
  have hNpos : 0 < N := lt_of_lt_of_le hn₁ (le_max_left n₁ n₂)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  set L := Real.log (N : ℝ) with hL
  set q : ℕ := max 1 ⌈β * L⌉₊ with hq
  -- first: m/N ≥ β L  (divide the lower bound by N)
  have hmN : (m : ℝ) / (N : ℝ) ≥ β * L := by
    rw [ge_iff_le, le_div_iff₀ hNR]
    calc β * L * (N : ℝ) = β * (N : ℝ) * L := by ring
      _ ≤ (m : ℝ) := hmLower
  -- N ≥ 2 : β L ≥ β log 2 > 2 log 2 > 1
  have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hLpos : Real.log 2 ≤ L := by
    rw [hL]; exact Real.log_le_log (by norm_num) hN2R
  have hlog2 : (0.6931471 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hbetaL : 1 ≤ β * L := by
    have hLge : (0.6931471 : ℝ) ≤ L := le_trans hlog2 hLpos
    have hLnn : 0 ≤ L := le_trans (by norm_num) hLge
    nlinarith [hLge, hβ.le, hLnn]
  -- q = max 1 ⌈β L⌉ = ⌈β L⌉ since β L ≥ 1
  have hceil_ge1 : 1 ≤ ⌈β * L⌉₊ := by
    rw [Nat.one_le_ceil_iff]; linarith
  have hq_eq : q = ⌈β * L⌉₊ := by rw [hq]; omega
  have hqR : (q : ℝ) ≤ β * L + 1 := by
    rw [hq_eq]
    have := Nat.ceil_lt_add_one (a := β * L) (by linarith : (0:ℝ) ≤ β * L)
    linarith
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · -- q ≥ β L
    have hceil : (⌈β * L⌉₊ : ℝ) ≥ β * L := Nat.le_ceil _
    have : (q : ℝ) ≥ (⌈β * L⌉₊ : ℝ) := by
      have := le_max_right 1 ⌈β * L⌉₊
      exact_mod_cast this
    exact le_trans hceil this
  · -- q ≤ 2 β L
    have : β * L + 1 ≤ 2 * (β * L) := by linarith [hbetaL]
    linarith [hqR, this]
  · -- q ≤ 2 m / N
    have hstep : β * L + 1 ≤ 2 * ((m : ℝ) / (N : ℝ)) := by
      have h2bL : β * L + 1 ≤ 2 * (β * L) := by linarith [hbetaL]
      have : 2 * (β * L) ≤ 2 * ((m : ℝ) / (N : ℝ)) := by linarith [hmN]
      linarith
    linarith [hqR, hstep]

/-! ### Final arithmetic packaging -/

/-- `n ≤ e^q` from `q ≥ β log N`, `n ≤ N`, `β > 1`, `N ≥ 1`. -/
lemma nat_le_exp_q (n N q : ℕ) (β L : ℝ)
    (hβ : 1 ≤ β) (hL : L = Real.log (N : ℝ)) (hNpos : 0 < N)
    (hnN : n ≤ N) (hqL : (q : ℝ) ≥ β * L) :
    (n : ℝ) ≤ Real.exp (q : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  -- N = exp(log N) = exp L ≤ exp(β L) ≤ exp q
  have hLnn : 0 ≤ L := by rw [hL]; exact Real.log_nonneg (by exact_mod_cast hNpos)
  have h1 : L ≤ β * L := by nlinarith [hLnn, hβ]
  have h2 : (N : ℝ) = Real.exp L := by rw [hL, Real.exp_log hNR]
  calc (n : ℝ) ≤ (N : ℝ) := hnR
    _ = Real.exp L := h2
    _ ≤ Real.exp (β * L) := Real.exp_le_exp.mpr h1
    _ ≤ Real.exp (q : ℝ) := Real.exp_le_exp.mpr hqL

open MatrixCompletion in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) →
        2 ≤ max n₁ n₂ →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂))) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (C * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  refine ⟨8 * Real.exp 1, by positivity, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hmLower hN2
  classical
  set N := max n₁ n₂ with hN
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hNpos : 0 < N := lt_of_lt_of_le hn₁ (le_max_left n₁ n₂)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hn₁N : (n₁ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_left n₁ n₂
  have hn₂N : (n₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right n₁ n₂
  -- Under hN2 (N ≥ 2) and hmLower, m = 0 is impossible: βNlogN > 0.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exfalso
    subst hm0
    have hN2' : 2 ≤ N := by rw [hN]; exact hN2
    have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2'
    have hlogN_pos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by linarith : (1 : ℝ) < (N : ℝ))
    have hmlow : β * (N : ℝ) * Real.log (N : ℝ) ≤ 0 := by
      rw [hN] at hmLower ⊢; simpa using hmLower
    have hpos : 0 < β * (N : ℝ) * Real.log (N : ℝ) := by
      have hβpos : (0 : ℝ) < β := by linarith
      exact mul_pos (mul_pos hβpos hNR) hlogN_pos
    linarith [hmlow, hpos]
  · -- m ≥ 1 : use the relaxed window
    have hN2' : 2 ≤ max n₁ n₂ := by rw [← hN]; exact hN2
    obtain ⟨q, hq1, hqL, hq2bL, hq2mN⟩ :=
      q_window_two_np β hβ n₁ n₂ m hn₁ hn₂ hmpos hmLower hN2'
    refine ⟨q, hq1, hqL, ?h2bL, ?h2pN, ?_⟩
    case h2bL =>
      -- (q:ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂)))
      simpa [hN] using hq2bL
    case h2pN =>
      -- (q:ℝ) ≤ 2 * (p * N)  with p = m/(n₁n₂)
      have hn₁R' : (0 : ℝ) < (n₁ : ℝ) := hn₁R
      have hn₂R' : (0 : ℝ) < (n₂ : ℝ) := hn₂R
      have hmR0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
      -- n₁n₂ ≤ N²
      have hn1N : (n₁ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_left n₁ n₂
      have hn2N : (n₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right n₁ n₂
      have hprodN : (n₁ : ℝ) * (n₂ : ℝ) ≤ (N : ℝ) * (N : ℝ) :=
        mul_le_mul hn1N hn2N (le_of_lt hn₂R') (le_of_lt (lt_of_lt_of_le hn₁R' hn1N))
      -- m/N ≤ m*N/(n₁n₂)
      have hkey : (m : ℝ) / (N : ℝ) ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (N : ℝ) := by
        rw [div_mul_eq_mul_div,
          div_le_div_iff₀ hNR (by positivity : (0:ℝ) < (n₁:ℝ)*(n₂:ℝ))]
        have hmono : (m : ℝ) * ((n₁ : ℝ) * (n₂ : ℝ)) ≤ (m : ℝ) * ((N : ℝ) * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hprodN hmR0
        nlinarith [hmono]
      calc (q : ℝ) ≤ 2 * ((m : ℝ) / (N : ℝ)) := by simpa [hN] using hq2mN
        _ ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (N : ℝ)) := by linarith [hkey]
        _ = 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂) : ℝ)) := by rw [hN]
    -- 0 ≤ p ≤ 1
    have hp0 : 0 ≤ p := by rw [hp]; positivity
    have hp1 : p ≤ 1 := by
      rw [hp, div_le_one (by positivity)]
      have : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
        have := hm; push_cast; exact_mod_cast this
      linarith
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hsup_nn : 0 ≤ entrySupNorm X := by
      by_cases h₁ : IsEmpty (Fin n₁)
      · exact le_of_eq (by haveI := h₁; simp [entrySupNorm])
      · by_cases h₂ : IsEmpty (Fin n₂)
        · exact le_of_eq (by haveI := h₂; simp [entrySupNorm])
        · have hn1 : Nonempty (Fin n₁) := not_isEmpty_iff.mp h₁
          have hn2 : Nonempty (Fin n₂) := not_isEmpty_iff.mp h₂
          rcases hn1 with ⟨i0⟩; rcases hn2 with ⟨j0⟩
          exact le_trans (abs_nonneg (X i0 j0))
            (le_trans
              (le_ciSup (Finite.bddAbove_range (fun j : Fin n₂ => |X i0 j|)) j0)
              (le_ciSup
                (Finite.bddAbove_range (fun i : Fin n₁ => ⨆ j : Fin n₂, |X i j|)) i0))
    -- `n₂·p = m/n₁ ≥ m/N`, `n₁·p = m/n₂ ≥ m/N`; both ≥ m/N ≥ q/2 and ≥ 1/2.
    have hn2p : (n₂ : ℝ) * p = (m : ℝ) / (n₁ : ℝ) := by
      rw [hp]; field_simp
    have hn1p : (n₁ : ℝ) * p = (m : ℝ) / (n₂ : ℝ) := by
      rw [hp]; field_simp
    have hmN_le_mn1 : (m : ℝ) / (N : ℝ) ≤ (m : ℝ) / (n₁ : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hn₁R hn₁N
    have hmN_le_mn2 : (m : ℝ) / (N : ℝ) ≤ (m : ℝ) / (n₂ : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hn₂R hn₂N
    -- relaxed constraints
    have hq2n2p : (q : ℝ) ≤ 2 * ((n₂ : ℝ) * p) := by
      rw [hn2p]; linarith [hq2mN, hmN_le_mn1]
    have hq2n1p : (q : ℝ) ≤ 2 * ((n₁ : ℝ) * p) := by
      rw [hn1p]; linarith [hq2mN, hmN_le_mn2]
    have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have h1_2n2p : 1 ≤ 2 * ((n₂ : ℝ) * p) := by linarith [hqR1, hq2n2p]
    have h1_2n1p : 1 ≤ 2 * ((n₁ : ℝ) * p) := by linarith [hqR1, hq2n1p]
    -- Nonempty instances
    haveI hne1 : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
    haveI hne2 : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
    -- e^q facts: n₁ ≤ e^q, n₂ ≤ e^q
    have hLdef : Real.log (N : ℝ) = Real.log (N : ℝ) := rfl
    have hn1_exp : (n₁ : ℝ) ≤ Real.exp (q : ℝ) :=
      nat_le_exp_q n₁ N q β (Real.log (N:ℝ)) (le_of_lt (lt_trans one_lt_two hβ)) rfl hNpos
        (le_max_left n₁ n₂) hqL
    have hn2_exp : (n₂ : ℝ) ≤ Real.exp (q : ℝ) :=
      nat_le_exp_q n₂ N q β (Real.log (N:ℝ)) (le_of_lt (lt_trans one_lt_two hβ)) rfl hNpos
        (le_max_right n₁ n₂) hqL
    -- Convert to bExp and split.
    rw [bernoulliExpectation_eq_bExp]
    -- pointwise max^q ≤ rowE^q + colE^q
    have hpt : ∀ Omega : Finset (Fin n₁ × Fin n₂),
        (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) ^ q
          ≤ (sampledRowEnergyMax Omega X) ^ q + (sampledColumnEnergyMax Omega X) ^ q := by
      intro Omega
      have hrnn0 : 0 ≤ sampledRowEnergyMax Omega X := by
        unfold sampledRowEnergyMax
        exact Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => by positivity))
      have hcnn0 : 0 ≤ sampledColumnEnergyMax Omega X := by
        unfold sampledColumnEnergyMax
        exact Real.iSup_nonneg (fun j => Finset.sum_nonneg (fun i _ => by positivity))
      rcases le_total (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) with hle | hle
      · rw [max_eq_right hle]
        have hrnn : 0 ≤ (sampledRowEnergyMax Omega X) ^ q := pow_nonneg hrnn0 q
        linarith [hrnn]
      · rw [max_eq_left hle]
        have hcnn : 0 ≤ (sampledColumnEnergyMax Omega X) ^ q := pow_nonneg hcnn0 q
        linarith [hcnn]
    have hsplit :
        CR2008Lemma62Max.bExp p
            (fun Omega => (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) ^ q)
          ≤ CR2008Lemma62Max.bExp p (fun Omega => (sampledRowEnergyMax Omega X) ^ q)
            + CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnEnergyMax Omega X) ^ q) := by
      rw [← CR2008Lemma62Max.bExp_add]
      exact CR2008Lemma62Max.bExp_mono hp0 hp1 hpt
    -- ROW part bound
    have hrow_part :
        CR2008Lemma62Max.bExp p (fun Omega => (sampledRowEnergyMax Omega X) ^ q)
          ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
      -- rowE^q ≤ (sup²)^q (rowCountMax)^q
      have hstep1 :
          CR2008Lemma62Max.bExp p (fun Omega => (sampledRowEnergyMax Omega X) ^ q)
            ≤ CR2008Lemma62Max.bExp p
                (fun Omega : Finset (Fin n₁ × Fin n₂) =>
                  (entrySupNorm X ^ 2) ^ q * (sampledRowCountMax Omega) ^ q) := by
        apply CR2008Lemma62Max.bExp_mono hp0 hp1
        intro Omega
        have hb := sampledRowEnergyMax_le Omega X
        have hrnn : 0 ≤ sampledRowEnergyMax Omega X := by
          unfold sampledRowEnergyMax
          exact Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => by positivity))
        calc (sampledRowEnergyMax Omega X) ^ q
            ≤ (entrySupNorm X ^ 2 * sampledRowCountMax Omega) ^ q :=
              pow_le_pow_left₀ hrnn hb q
          _ = (entrySupNorm X ^ 2) ^ q * (sampledRowCountMax Omega) ^ q := mul_pow _ _ q
      rw [CR2008Lemma62Max.bExp_smul] at hstep1
      -- bExp[(rowCountMax)^q] = bExp[(⨆ i rowCount)^q] ≤ n₁ (4 n₂ p)^q
      have hcm : ∀ Omega : Finset (Fin n₁ × Fin n₂),
          (sampledRowCountMax Omega) ^ q
            = (⨆ i : Fin n₁, (CR2008Lemma62Max.rowCount Omega i : ℝ)) ^ q := by
        intro Omega; rw [sampledRowCountMax_eq_iSup]
      have hmax :
          CR2008Lemma62Max.bExp p
              (fun Omega : Finset (Fin n₁ × Fin n₂) => (sampledRowCountMax Omega) ^ q)
            ≤ (n₁ : ℝ) * (4 * ((n₂ : ℝ) * p)) ^ q := by
        rw [show (fun Omega : Finset (Fin n₁ × Fin n₂) => (sampledRowCountMax Omega) ^ q)
              = (fun Omega => (⨆ i : Fin n₁, (CR2008Lemma62Max.rowCount Omega i : ℝ)) ^ q)
            from funext hcm]
        exact CR2008Lemma62Max.bExp_max_rowCount_pow_le hp0 hp1 q
          ((4 * ((n₂ : ℝ) * p)) ^ q)
          (fun a => per_row_bound p a q hp0 hp1 hq2n2p h1_2n2p)
      -- assemble: (sup²)^q * bExp ≤ (sup²)^q * (n₁ (4 n₂ p)^q) ≤ (4e N p sup²)^q
      have hsupq_nn : 0 ≤ (entrySupNorm X ^ 2) ^ q := by positivity
      calc CR2008Lemma62Max.bExp p (fun Omega => (sampledRowEnergyMax Omega X) ^ q)
          ≤ (entrySupNorm X ^ 2) ^ q *
              CR2008Lemma62Max.bExp p (fun Omega => (sampledRowCountMax Omega) ^ q) := hstep1
        _ ≤ (entrySupNorm X ^ 2) ^ q * ((n₁ : ℝ) * (4 * ((n₂ : ℝ) * p)) ^ q) :=
              mul_le_mul_of_nonneg_left hmax hsupq_nn
        _ ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
              -- n₁ ≤ e^q, n₂ ≤ N, repackage
              have hn2p_nn : 0 ≤ (n₂ : ℝ) * p := by positivity
              have h4 : 0 ≤ 4 * ((n₂ : ℝ) * p) := by positivity
              -- (sup²)^q n₁ (4 n₂ p)^q = n₁ * (4 n₂ p sup²)^q ≤ e^q (4 N p sup²)^q
              have hrw :
                  (entrySupNorm X ^ 2) ^ q * ((n₁ : ℝ) * (4 * ((n₂ : ℝ) * p)) ^ q)
                    = (n₁ : ℝ) * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := by
                rw [mul_pow]; ring
              rw [hrw]
              have hbase_nn : 0 ≤ 4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2 := by positivity
              -- n₁ ≤ e^q
              have hstepA : (n₁ : ℝ) * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q
                  ≤ Real.exp (q : ℝ) * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q :=
                mul_le_mul_of_nonneg_right hn1_exp (by positivity)
              -- e^q = (e)^q ; (4 n₂ p sup²) ≤ (4 N p sup²)
              have hexpq : Real.exp (q : ℝ) = (Real.exp 1) ^ q := by
                rw [← Real.exp_nat_mul]; ring_nf
              have hbase_le : 4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2
                  ≤ 4 * ((N : ℝ) * p) * entrySupNorm X ^ 2 := by
                have hstep : (n₂ : ℝ) * p ≤ (N : ℝ) * p :=
                  mul_le_mul_of_nonneg_right hn₂N hp0
                have h4 : 4 * ((n₂ : ℝ) * p) ≤ 4 * ((N : ℝ) * p) :=
                  mul_le_mul_of_nonneg_left hstep (by norm_num)
                exact mul_le_mul_of_nonneg_right h4 (sq_nonneg (entrySupNorm X))
              calc (n₁ : ℝ) * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q
                  ≤ Real.exp (q:ℝ) * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := hstepA
                _ = (Real.exp 1) ^ q * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := by
                      rw [hexpq]
                _ ≤ (Real.exp 1) ^ q * (4 * ((N : ℝ) * p) * entrySupNorm X ^ 2) ^ q :=
                      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hbase_le q)
                        (by positivity)
                _ = (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
                      rw [← mul_pow]; ring_nf
    -- COLUMN part bound (symmetric)
    have hcol_part :
        CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnEnergyMax Omega X) ^ q)
          ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
      have hstep1 :
          CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnEnergyMax Omega X) ^ q)
            ≤ CR2008Lemma62Max.bExp p
                (fun Omega : Finset (Fin n₁ × Fin n₂) =>
                  (entrySupNorm X ^ 2) ^ q * (sampledColumnCountMax Omega) ^ q) := by
        apply CR2008Lemma62Max.bExp_mono hp0 hp1
        intro Omega
        have hb := sampledColumnEnergyMax_le Omega X
        have hcnn : 0 ≤ sampledColumnEnergyMax Omega X := by
          unfold sampledColumnEnergyMax
          exact Real.iSup_nonneg (fun j => Finset.sum_nonneg (fun i _ => by positivity))
        calc (sampledColumnEnergyMax Omega X) ^ q
            ≤ (entrySupNorm X ^ 2 * sampledColumnCountMax Omega) ^ q :=
              pow_le_pow_left₀ hcnn hb q
          _ = (entrySupNorm X ^ 2) ^ q * (sampledColumnCountMax Omega) ^ q := mul_pow _ _ q
      rw [CR2008Lemma62Max.bExp_smul] at hstep1
      -- sampledColumnCountMax Omega = ⨆ j, colCount Omega j
      have hccm : ∀ Omega : Finset (Fin n₁ × Fin n₂),
          (sampledColumnCountMax Omega) ^ q
            = (⨆ j : Fin n₂, (colCount Omega j : ℝ)) ^ q := by
        intro Omega
        unfold sampledColumnCountMax
        congr 1
        congr 1
        ext j
        unfold colCount
        rw [Finset.sum_boole]
      have hmax :
          CR2008Lemma62Max.bExp p
              (fun Omega : Finset (Fin n₁ × Fin n₂) => (sampledColumnCountMax Omega) ^ q)
            ≤ (n₂ : ℝ) * (4 * ((n₁ : ℝ) * p)) ^ q := by
        rw [show (fun Omega : Finset (Fin n₁ × Fin n₂) => (sampledColumnCountMax Omega) ^ q)
              = (fun Omega => (⨆ j : Fin n₂, (colCount Omega j : ℝ)) ^ q)
            from funext hccm]
        -- max over columns: same engine, with colCount.  Use bExp_max via a colCount version.
        -- reuse bExp_max_rowCount_pow_le on the swapped product? simpler: build directly.
        have hpt2 : ∀ Omega : Finset (Fin n₁ × Fin n₂),
            (⨆ j : Fin n₂, (colCount Omega j : ℝ)) ^ q
              ≤ ∑ j : Fin n₂, ((colCount Omega j : ℝ)) ^ q :=
          fun Omega => CR2008Lemma62Max.max_pow_le_sum_pow
            (fun j => (colCount Omega j : ℝ)) (fun j => by positivity) q
        calc CR2008Lemma62Max.bExp p (fun Omega => (⨆ j : Fin n₂, (colCount Omega j : ℝ)) ^ q)
            ≤ CR2008Lemma62Max.bExp p
                (fun Omega => ∑ j : Fin n₂, ((colCount Omega j : ℝ)) ^ q) :=
              CR2008Lemma62Max.bExp_mono hp0 hp1 hpt2
          _ = ∑ j : Fin n₂, CR2008Lemma62Max.bExp p
                (fun Omega => ((colCount Omega j : ℝ)) ^ q) :=
              CR2008Lemma62Max.bExp_sum p Finset.univ
                (fun j Omega => ((colCount Omega j : ℝ)) ^ q)
          _ ≤ ∑ _j : Fin n₂, (4 * ((n₁ : ℝ) * p)) ^ q :=
              Finset.sum_le_sum (fun j _ => per_col_bound p j q hp0 hp1 hq2n1p h1_2n1p)
          _ = (n₂ : ℝ) * (4 * ((n₁ : ℝ) * p)) ^ q := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsupq_nn : 0 ≤ (entrySupNorm X ^ 2) ^ q := by positivity
      calc CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnEnergyMax Omega X) ^ q)
          ≤ (entrySupNorm X ^ 2) ^ q *
              CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnCountMax Omega) ^ q) := hstep1
        _ ≤ (entrySupNorm X ^ 2) ^ q * ((n₂ : ℝ) * (4 * ((n₁ : ℝ) * p)) ^ q) :=
              mul_le_mul_of_nonneg_left hmax hsupq_nn
        _ ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
              have hrw :
                  (entrySupNorm X ^ 2) ^ q * ((n₂ : ℝ) * (4 * ((n₁ : ℝ) * p)) ^ q)
                    = (n₂ : ℝ) * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := by
                rw [mul_pow]; ring
              rw [hrw]
              have hbase_nn : 0 ≤ 4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2 := by positivity
              have hstepA : (n₂ : ℝ) * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q
                  ≤ Real.exp (q : ℝ) * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q :=
                mul_le_mul_of_nonneg_right hn2_exp (by positivity)
              have hexpq : Real.exp (q : ℝ) = (Real.exp 1) ^ q := by
                rw [← Real.exp_nat_mul]; ring_nf
              have hbase_le : 4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2
                  ≤ 4 * ((N : ℝ) * p) * entrySupNorm X ^ 2 := by
                have hstep : (n₁ : ℝ) * p ≤ (N : ℝ) * p :=
                  mul_le_mul_of_nonneg_right hn₁N hp0
                have h4 : 4 * ((n₁ : ℝ) * p) ≤ 4 * ((N : ℝ) * p) :=
                  mul_le_mul_of_nonneg_left hstep (by norm_num)
                exact mul_le_mul_of_nonneg_right h4 (sq_nonneg (entrySupNorm X))
              calc (n₂ : ℝ) * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q
                  ≤ Real.exp (q:ℝ) * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := hstepA
                _ = (Real.exp 1) ^ q * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := by
                      rw [hexpq]
                _ ≤ (Real.exp 1) ^ q * (4 * ((N : ℝ) * p) * entrySupNorm X ^ 2) ^ q :=
                      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hbase_le q)
                        (by positivity)
                _ = (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
                      rw [← mul_pow]; ring_nf
    -- Combine row + col ≤ 2 (4e N p sup²)^q ≤ (8e N p sup²)^q = RHS
    have hAnn : 0 ≤ 4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2 := by positivity
    have hfinal :
        (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q
          + (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q
          ≤ (8 * Real.exp 1 * p * (N : ℝ) * entrySupNorm X ^ 2) ^ q := by
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ q := by
        calc (2:ℝ) = 2^1 := by norm_num
          _ ≤ 2^q := pow_le_pow_right₀ (by norm_num) hq1
      have hrw : (8 * Real.exp 1 * p * (N : ℝ) * entrySupNorm X ^ 2) ^ q
          = (2:ℝ)^q * (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
        rw [← mul_pow]; ring_nf
      rw [hrw, ← two_mul]
      have hpowAnn : 0 ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by positivity
      exact mul_le_mul_of_nonneg_right h2 hpowAnn
    -- finish
    calc CR2008Lemma62Max.bExp p
            (fun Omega => (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) ^ q)
        ≤ CR2008Lemma62Max.bExp p (fun Omega => (sampledRowEnergyMax Omega X) ^ q)
            + CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnEnergyMax Omega X) ^ q) := hsplit
      _ ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q
            + (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q :=
            add_le_add hrow_part hcol_part
      _ ≤ (8 * Real.exp 1 * p * (N : ℝ) * entrySupNorm X ^ 2) ^ q := hfinal

end Sol2pNctrl

open MatrixCompletion in
theorem bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) →
        2 ≤ max n₁ n₂ →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂))) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (C * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q :=
  Sol2pNctrl.solution



end MatrixCompletion.MatrixSamplingReuse_d9cc9674
export MatrixCompletion.MatrixSamplingReuse_d9cc9674 (bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN)

/- Complete accepted-source reuse: theorem c0188309-6fd2-4977-a823-31e1aa3eee1e; submission 84cc520d-97f3-4fbd-aaac-6e2b0d917c75.
Original SHA256 252cf2cbbd05955213f7b0ab6692097206d78d70ce0aba02135568ef6a353c30. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to sample_ratio_between_zero_and_one.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_c0188309

open MatrixCompletion

theorem sample_ratio_between_zero_and_one
    (n₁ n₂ m : ℕ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ∧
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 := by
  intro hn₁ hn₂ hm
  constructor
  · exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by
      exact mul_pos (Nat.cast_pos.mpr hn₁) (Nat.cast_pos.mpr hn₂)
    have hnum_le_den : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
      exact_mod_cast hm
    rw [div_le_iff₀ hden_pos]
    simpa using hnum_le_den


end MatrixCompletion.MatrixSamplingReuse_c0188309
export MatrixCompletion.MatrixSamplingReuse_c0188309 (sample_ratio_between_zero_and_one)

/- Complete accepted-source reuse: theorem 6585113d-18c8-4106-b87c-18196b77d0cf; submission 1f6e1050-5554-43ac-b321-db7fa83ba280.
Original SHA256 fd2f6b876e7690fef02903ce713f3003e91a599c3da84b7426301251ce0c77ad. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_6585113d

open MatrixCompletion

open scoped Classical BigOperators

/-!
Source: Candes-Recht, "Exact Matrix Completion via Convex Optimization",
Section 6.1, PDF p. 24 in the local copy.  The paragraph beginning "Since the
function `f(S)=||S||^q` is convex, Jensen's inequality gives..." derives
`E ||S||^q <= E ||S - S'||^q`, where `S'` is an independent copy of the
centered sampled matrix.

Reduction: the child theorem is the pointwise-in-`Omega` Jensen inequality.
The present parent theorem integrates that pointwise inequality over `Omega`.
The sample-ratio hypotheses give `p in [0,1]`, so all Bernoulli weights are
nonnegative and the finite sum is monotone.
-/

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

theorem centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        bernoulliPairExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega Omega' =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                centeredSamplingFluctuation Omega'
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) := by
  intro n₁ n₂ m q X hn₁ hn₂ hm hq
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp, hp_one⟩
  have hPointwise :=
    centered_sampling_jensen_pointwise_independent_copy_bound_of_sample_ratio
      n₁ n₂ m q X hn₁ hn₂ hm hq
  change
    bernoulliExpectation p
        (fun Omega =>
          spectralNorm (centeredSamplingFluctuation Omega p X) ^ q) ≤
      bernoulliPairExpectation p
        (fun Omega Omega' =>
          spectralNorm
            (centeredSamplingFluctuation Omega p X -
              centeredSamplingFluctuation Omega' p X) ^ q)
  unfold bernoulliExpectation bernoulliPairExpectation
  apply Finset.sum_le_sum
  intro Omega _hOmega
  have hweight_nonneg : 0 ≤ bernoulliObservationWeight p Omega :=
    bernoulliObservationWeight_nonneg hp hp_one Omega
  have hOmegaPointwise :
      spectralNorm (centeredSamplingFluctuation Omega p X) ^ q ≤
        ∑ Omega' : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega' *
            spectralNorm
              (centeredSamplingFluctuation Omega p X -
                centeredSamplingFluctuation Omega' p X) ^ q := by
    simpa [p, bernoulliExpectation] using hPointwise Omega
  calc
    bernoulliObservationWeight p Omega *
        spectralNorm (centeredSamplingFluctuation Omega p X) ^ q
        ≤ bernoulliObservationWeight p Omega *
          (∑ Omega' : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Omega' *
              spectralNorm
                (centeredSamplingFluctuation Omega p X -
                  centeredSamplingFluctuation Omega' p X) ^ q) := by
          exact mul_le_mul_of_nonneg_left hOmegaPointwise hweight_nonneg
    _ =
        ∑ Omega' : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega *
            bernoulliObservationWeight p Omega' *
              spectralNorm
                (centeredSamplingFluctuation Omega p X -
                  centeredSamplingFluctuation Omega' p X) ^ q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro Omega' _hOmega'
          ring

end MatrixCompletion.MatrixSamplingReuse_6585113d
export MatrixCompletion.MatrixSamplingReuse_6585113d (centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio)

/- Complete accepted-source reuse: theorem 2fe65578-8337-45d7-95f1-0aa6df4d35cd; submission c8311c07-49da-42c5-8be0-44bacd399d14.
Original SHA256 caa3e99f8f3f65418cdbeada9104d36d9c9c4cc2c55dfa321ece1b8c396212d6. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to centered_sampling_symmetrization_moment_bound_of_sample_ratio.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_2fe65578

open MatrixCompletion
open scoped BigOperators Classical

/-- `centered_sampling_symmetrization_moment_bound_of_sample_ratio`.
Composes the three symmetrization steps (Candès–Recht 2009/2012, §6.1):
  (1) Jensen independent-copy moment bound `E‖F‖^q ≤ E_pair‖F(Ω)−F(Ω')‖^q`
      (`centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio`);
  (2) Rademacher symmetrization `E_pair‖F(Ω)−F(Ω')‖^q ≤ E_pair E_ε‖A(Ω,ε)−A(Ω',ε)‖^q`
      (`centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio`);
  (3) triangle `E_pair E_ε‖A(Ω,ε)−A(Ω',ε)‖^q ≤ Csym^q · E_Ω E_ε‖A(Ω,ε)‖^q`
      (`rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio`).
The `Csym` is inherited from step (3). -/
theorem centered_sampling_symmetrization_moment_bound_of_sample_ratio :
    ∃ Csym : ℝ, 0 < Csym ∧
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          Csym ^ q *
            bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                rademacherExpectation
                  (fun eps =>
                    spectralNorm
                      (rademacherSampledMatrix Omega eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) := by
  obtain ⟨Csym, hCsym, hsym⟩ :=
    rademacher_sampled_difference_moment_le_single_sample_moment_of_sample_ratio
  refine ⟨Csym, hCsym, ?_⟩
  intro n₁ n₂ m q X hn₁ hn₂ hm hq
  have h1 := centered_sampling_jensen_independent_copy_moment_bound_of_sample_ratio
    n₁ n₂ m q X hn₁ hn₂ hm hq
  have h2 := centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio
    n₁ n₂ m q X hn₁ hn₂ hm hq
  have h3 := hsym n₁ n₂ m q X hn₁ hn₂ hm hq
  exact le_trans h1 (le_trans h2 h3)

end MatrixCompletion.MatrixSamplingReuse_2fe65578
export MatrixCompletion.MatrixSamplingReuse_2fe65578 (centered_sampling_symmetrization_moment_bound_of_sample_ratio)

/- Complete accepted-source reuse: theorem 7792bb68-7fef-4199-8c86-226bd5c0f6e8; submission cd3ac9da-01b5-45aa-aa92-a7c709a7b6c4.
Original SHA256 c173f14cd4f50bc0cf49ad257b48e4c8db67126713ec9338449556c86e753a41. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to centered_sampling_log_moment_khintchine_scale_from_symmetrization_and_rademacher.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_7792bb68

open MatrixCompletion

/-- Apply the abstract moment-transitivity lemma to the centered-sampling
moment and the Rademacher auxiliary moment. -/
theorem centered_sampling_log_moment_khintchine_scale_from_symmetrization_and_rademacher
    (Csym Crad : ℝ) :
    0 < Csym →
    0 < Crad →
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        1 ≤ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          Csym ^ q *
            bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                rademacherExpectation
                  (fun eps =>
                    spectralNorm
                      (rademacherSampledMatrix Omega eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              rademacherExpectation
                (fun eps =>
                  spectralNorm
                    (rademacherSampledMatrix Omega eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Cq * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  intro hCsym hCrad
  rcases bernoulli_moment_bound_from_symmetrization_and_auxiliary_moment_bound
      Csym Crad hCsym hCrad with
    ⟨Cq, hCq, hMoment⟩
  refine ⟨Cq, hCq, ?_⟩
  intro n₁ n₂ m q X hq hSymm hRad
  have hRad' :
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
        (Crad *
          (Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X)) ^ q := by
    simpa [mul_assoc] using hRad
  have h :=
    hMoment
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
    (Real.sqrt
      (((q : ℝ) * (↑(max n₁ n₂))) /
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
      entrySupNorm X)
    q
    (fun Omega =>
      spectralNorm
        (centeredSamplingFluctuation Omega
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)
    (fun Omega =>
      rademacherExpectation
        (fun eps =>
          spectralNorm
            (rademacherSampledMatrix Omega eps
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q))
    hq hSymm hRad'
  simpa [mul_assoc] using h


end MatrixCompletion.MatrixSamplingReuse_7792bb68
export MatrixCompletion.MatrixSamplingReuse_7792bb68 (centered_sampling_log_moment_khintchine_scale_from_symmetrization_and_rademacher)

/- Complete accepted-source reuse: theorem ebe239aa-9d10-4e5e-b0c8-70bcfb207d86; submission bed5b463-db8d-4362-b232-51a804ac1005.
Original SHA256 2fe287df9c55cb2781d3b67dad2cd834481c7b47bba13a083adde3259a350dfb. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to centered_sampling_log_moment_scale_absorption.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_ebe239aa

open MatrixCompletion

/-- Split the Section 6.1 scale absorption into the expectation-transitivity
step from symmetrization/Rademacher bounds and the algebraic absorption
`q ≤ 2 β log n`. -/
theorem centered_sampling_log_moment_scale_absorption
    (Csym Crad : ℝ) :
    0 < Csym →
    0 < Crad →
    ∃ Cmoment : ℝ, 0 < Cmoment ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          Csym ^ q *
            bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                rademacherExpectation
                  (fun eps =>
                    spectralNorm
                      (rademacherSampledMatrix Omega eps
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              rademacherExpectation
                (fun eps =>
                  spectralNorm
                    (rademacherSampledMatrix Omega eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Cmoment * Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  intro hCsym hCrad
  rcases
      centered_sampling_log_moment_khintchine_scale_from_symmetrization_and_rademacher
        Csym Crad hCsym hCrad with
    ⟨Cq, hCq, hKhintchineScale⟩
  rcases centered_sampling_log_moment_beta_scale_from_khintchine_scale
      Cq hCq with
    ⟨Cmoment, hCmoment, hBetaScale⟩
  refine ⟨Cmoment, hCmoment, ?_⟩
  intro β hβ n₁ n₂ m q X hn₁ hn₂ hm hSample
    hqOne hqLogLower hqLogUpper hSymm hRad
  have hQScale :=
    hKhintchineScale n₁ n₂ m q X hqOne hSymm hRad
  exact hBetaScale β hβ n₁ n₂ m q X
    hn₁ hn₂ hm hSample hqOne hqLogLower hqLogUpper hQScale


end MatrixCompletion.MatrixSamplingReuse_ebe239aa
export MatrixCompletion.MatrixSamplingReuse_ebe239aa (centered_sampling_log_moment_scale_absorption)

/- Complete accepted-source reuse: theorem fd9d68f3-8f4e-45dc-ad7d-eeece042b325; submission ba2cde31-2f9a-40e0-a64c-68b2b35a558e.
Original SHA256 a934222b125f993e8507ef468f9f479ad6d7d79000ff18f1d3f0066df159fccf. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to centered_sampling_log_moment_from_row_column_energy_2pN.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_fd9d68f3

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF pp. 24--25, Section 6.1.  The reduction
uses equation (6.5), the Jensen/Rademacher symmetrization paragraph on PDF
p. 24, Lemma 6.1 on PDF p. 25, and the displayed row/column-energy moment
estimate (6.6).  In Lean this node combines the sample-ratio-safe
symmetrization bound, the Rademacher/Khintchine row-column energy estimate, and
the already-proved scale absorption into the final log-moment estimate.

`_2pN` variant: the supplied exponent window is `q ≤ 2·p·n` instead of the
strict `q ≤ p·n`; the relaxed window is the one actually supplied by the
one-sample energy moment bound at `q = ⌈β log N⌉`.  The symmetrization and
scale-absorption children never consume any exponent window; only the middle
Rademacher/Khintchine child carries it, and it is dead weight there, so the
`_2pN` middle child applies verbatim. -/
theorem centered_sampling_log_moment_from_row_column_energy_2pN
    (Cenergy : ℝ) :
    0 < Cenergy →
    ∃ Cmoment : ℝ, 0 < Cmoment ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        (∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂))) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q) →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                spectralNorm
                  (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
            (Cmoment * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) ^ q := by
  intro hCenergy
  rcases centered_sampling_symmetrization_moment_bound_of_sample_ratio with
    ⟨Csym, hCsym, hSymm⟩
  rcases rademacher_sampled_matrix_moment_from_row_column_energy_2pN Cenergy
      hCenergy with
    ⟨Crad, hCrad, hRad⟩
  rcases centered_sampling_log_moment_scale_absorption Csym Crad
      hCsym hCrad with
    ⟨Cmoment, hCmoment, hScale⟩
  refine ⟨Cmoment, hCmoment, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hSample hEnergy
  rcases hEnergy with
    ⟨q, hqOne, hqLogLower, hqLogUpper, hqSamplingUpper, hEnergyBound⟩
  refine ⟨q, hqOne, hqLogLower, ?_⟩
  exact hScale β hβ n₁ n₂ m q X hn₁ hn₂ hm hSample hqOne
    hqLogLower hqLogUpper
    (hSymm n₁ n₂ m q X hn₁ hn₂ hm hqOne)
    (hRad β hβ n₁ n₂ m q X hn₁ hn₂ hm hSample hqOne
      hqLogLower hqLogUpper hqSamplingUpper hEnergyBound)

end MatrixCompletion.MatrixSamplingReuse_fd9d68f3
export MatrixCompletion.MatrixSamplingReuse_fd9d68f3 (centered_sampling_log_moment_from_row_column_energy_2pN)

/- Complete accepted-source reuse: theorem fe0df420-4db0-4480-866f-739ecf97d966; submission 4b61f11f-2128-45f4-ae80-8944363982db.
Original SHA256 34a3a97bdef66b0b2aecdeb33e96fd5eebacc62649331cb94b764894dc0f1f9c. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to fixed_matrix_centered_sampling_log_moment_bound.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_fe0df420

open MatrixCompletion

/-- Decompose the fixed-matrix log-moment estimate (`fe0df420`) into the
strengthened `_2pN` controlled sampled row/column energy moment estimate and
the `_2pN` noncommutative-Khintchine conversion.

DESIGN NOTE (the gap and its resolution).  The bare energy supplier `4337294c`
(`bernoulli_sampled_row_column_energy_log_moment_bound`) returns an existential
`∃ q, 1 ≤ q ∧ q ≥ β log N ∧ energybound`; it does NOT re-export `q ≤ 2 β log N`
or `q ≤ 2 p N`.  But the `_2pN` Khintchine conversion below needs BOTH of those
on the supplied `q`.  The honest fix is the strengthened supplier
`bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN`, which
re-exports the two upper bounds — both established by `4337294c`'s exponent
window lemma `q_window_two_np` (`q ≤ β log N + 1 ≤ 2 β log N` and
`q ≤ 2 m/N ≤ 2 p N`).  That strengthened supplier is only valid for `2 ≤ N`
(when `N = 1` we have `log N = 0`, so `2 β log N = 0` and no `q ≥ 1` fits the
upper window).  The `N = 1` degenerate case (`n₁ = n₂ = 1`) is therefore handled
DIRECTLY here: the only feasible sample sizes are `m ∈ {0, 1}` and in both the
centered sampling fluctuation is the zero matrix (`m = 1 ⇒ p = 1 ⇒ P_Ω = I`;
`m = 0 ⇒ p = 0` and `0⁻¹ = 0`), so the left-hand side is `0` and the bound holds
with `q := 1` (the right-hand side carries the factor `√(β·1·log 1) = 0`). -/
theorem fixed_matrix_centered_sampling_log_moment_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                spectralNorm
                  (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
            (C * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) ^ q := by
  classical
  rcases bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN with
    ⟨Cenergy, hCenergy, hEnergy⟩
  rcases centered_sampling_log_moment_from_row_column_energy_2pN Cenergy
      hCenergy with
    ⟨Cmoment, hCmoment, hKhintchine⟩
  refine ⟨Cmoment, hCmoment, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hSample
  by_cases hN2 : 2 ≤ max n₁ n₂
  · -- Non-degenerate regime: route through the strengthened supplier + `_2pN` Khintchine.
    exact hKhintchine β hβ n₁ n₂ m X hn₁ hn₂ hm hSample
      (hEnergy β hβ n₁ n₂ m X hn₁ hn₂ hm hSample hN2)
  · -- Degenerate `N = 1` regime: `max n₁ n₂ = 1`, so `n₁ = n₂ = 1` and `log N = 0`.
    push_neg at hN2
    -- `max n₁ n₂ < 2` and `0 < n₁, 0 < n₂` force `n₁ = n₂ = 1`.
    have hmax1 : max n₁ n₂ = 1 :=
      le_antisymm (Nat.lt_succ_iff.mp hN2) (le_trans hn₁ (le_max_left n₁ n₂))
    have hn₁1 : n₁ = 1 := le_antisymm (hmax1 ▸ le_max_left n₁ n₂) hn₁
    have hn₂1 : n₂ = 1 := le_antisymm (hmax1 ▸ le_max_right n₁ n₂) hn₂
    subst hn₁1; subst hn₂1
    refine ⟨1, le_refl 1, ?_, ?_⟩
    · -- q = 1 ≥ β log 1 = 0
      have hm1 : max 1 1 = 1 := rfl
      simp [hm1, Real.log_one]
    · -- LHS = 0: the surviving (positively weighted) fluctuation term is the zero matrix,
      -- so the whole Bernoulli expectation is 0; the RHS has the factor `√(β·1·log 1) = 0`.
      -- The right-hand side collapses to 0 first: `log (max 1 1) = log 1 = 0`,
      -- so `√(β·1·0/…) = 0` and the whole RHS is `(C·0·‖X‖)^1 = 0`.
      have hmaxcast : ((max (1 : ℕ) 1 : ℕ) : ℝ) = 1 := by norm_num
      rw [hmaxcast, Real.log_one, mul_zero, zero_div, Real.sqrt_zero,
        mul_zero, zero_mul, pow_one]
      -- Now show LHS ≤ 0 (the `pow_one` above already collapsed the inner power);
      -- combined with LHS ≥ 0 this forces LHS = 0.
      -- The universe `Finset (Fin 1 × Fin 1)` has exactly two elements: ∅ and {(0,0)}.
      -- Evaluate the expectation as a finite sum and discharge by `interval_cases m`.
      interval_cases m
      · -- m = 0 ⇒ p = 0.  weight(∅) = 1, weight of the full set = 0, and fluct(∅) = 0.
        unfold bernoulliExpectation bernoulliObservationWeight
        simp only [pow_one]
        apply Finset.sum_nonpos
        intro Omega _
        by_cases hΩ : Omega = (∅ : Finset (Fin 1 × Fin 1))
        · subst hΩ
          have : spectralNorm (centeredSamplingFluctuation (∅ : Finset (Fin 1 × Fin 1))
              ((0 : ℝ) / ((1 : ℝ) * (1 : ℝ))) X) = 0 := by
            have : centeredSamplingFluctuation (∅ : Finset (Fin 1 × Fin 1))
                ((0 : ℝ) / ((1 : ℝ) * (1 : ℝ))) X = 0 := by
              ext i j
              simp [centeredSamplingFluctuation, samplingProjection]
            rw [this]; unfold spectralNorm; simp
          simp only [Nat.cast_zero, Nat.cast_one] at this ⊢
          rw [this]; exact (mul_zero _).le
        · -- Ω ≠ ∅ ⇒ |Ω| ≥ 1 ⇒ weight = 0^|Ω|·… = 0.
          have hcard : 0 < Omega.card :=
            Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hΩ)
          have hz : ((0 : ℝ)) ^ Omega.card = 0 := zero_pow hcard.ne'
          simp only [Nat.cast_zero, zero_div, hz, zero_mul, mul_zero, le_refl]
      · -- m = 1 ⇒ p = 1.  weight(∅) = 0, weight(full) = 1, fluct(full) = 0.
        unfold bernoulliExpectation bernoulliObservationWeight
        simp only [pow_one]
        apply Finset.sum_nonpos
        intro Omega _
        by_cases hΩ : Omega = (Finset.univ : Finset (Fin 1 × Fin 1))
        · subst hΩ
          have hfz : centeredSamplingFluctuation (Finset.univ : Finset (Fin 1 × Fin 1))
              ((1 : ℝ) / ((1 : ℝ) * (1 : ℝ))) X = 0 := by
            ext i j
            fin_cases i; fin_cases j
            simp [centeredSamplingFluctuation, samplingProjection]
          have : spectralNorm (centeredSamplingFluctuation
              (Finset.univ : Finset (Fin 1 × Fin 1))
              ((1 : ℝ) / ((1 : ℝ) * (1 : ℝ))) X) = 0 := by
            rw [hfz]; unfold spectralNorm; simp
          simp only [Nat.cast_zero, Nat.cast_one] at this ⊢
          rw [this]; exact (mul_zero _).le
        · -- Ω ≠ univ ⇒ |Ωᶜ| ≥ 1 ⇒ card univ - |Ω| ≥ 1 ⇒ (1-1)^… = 0^… = 0.
          have hcardlt : Omega.card < Fintype.card (Fin 1 × Fin 1) := by
            rcases lt_or_eq_of_le (Finset.card_le_univ Omega) with h | h
            · simpa using h
            · exact absurd (Finset.card_eq_iff_eq_univ Omega |>.mp (by simpa using h)) hΩ
          have hpos : 0 < Fintype.card (Fin 1 × Fin 1) - Omega.card :=
            Nat.sub_pos_of_lt hcardlt
          have hz : ((0 : ℝ)) ^ (Fintype.card (Fin 1 × Fin 1) - Omega.card) = 0 :=
            zero_pow hpos.ne'
          have h11 : (1 : ℝ) / ((1 : ℝ) * (1 : ℝ)) = 1 := by norm_num
          simp only [Nat.cast_one, h11, sub_self, hz, mul_zero, zero_mul, le_refl]

end MatrixCompletion.MatrixSamplingReuse_fe0df420
export MatrixCompletion.MatrixSamplingReuse_fe0df420 (fixed_matrix_centered_sampling_log_moment_bound)

/- Complete accepted-source reuse: theorem f22de60f-3948-41a1-b8d7-d63e8dd8b56b; submission 0bc5bbd0-ed83-404e-a310-34854f4866ea.
Original SHA256 18b2b4079d45ece33f31dbeb83e095376f2476facdee7e91e1ca7a82792e0371. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_f22de60f

open MatrixCompletion

open scoped Classical BigOperators

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

private lemma sum_bernoulliObservationWeight_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} (_hp : 0 ≤ p) (_hp_one : p ≤ 1) :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega) = 1 := by
  classical
  let α := Fin n₁ × Fin n₂
  let N := Fintype.card α
  have hsum_powerset :
      (∑ Omega : Finset α,
          p ^ Omega.card * (1 - p) ^ (N - Omega.card)) =
        ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [← Finset.powerset_univ]
    rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k hk
    have hcard :
        (Finset.univ : Finset α).card = N := by
      simp [N]
    have h :=
      Finset.sum_powersetCard k (Finset.univ : Finset α)
        (fun j : ℕ => p ^ j * (1 - p) ^ (N - j))
    simpa [hcard, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega)
        = ∑ Omega : Finset α,
            p ^ Omega.card * (1 - p) ^ (N - Omega.card) := by
          simp [α, N, bernoulliObservationWeight]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := hsum_powerset
    _ = ∑ k ∈ Finset.range (N + 1),
          p ^ k * (1 - p) ^ (N - k) * (Nat.choose N k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (p + (1 - p)) ^ N := by
          rw [add_pow]
    _ = 1 := by
          ring

private lemma spectralNorm_nonneg {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    0 ≤ spectralNorm X := by
  unfold spectralNorm
  exact norm_nonneg _

private lemma bernoulliEventProb_add_compl
    {n₁ n₂ : ℕ} {p : ℝ} (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p Event +
        (∑ Omega : Finset (Fin n₁ × Fin n₂),
          if Event Omega then 0 else bernoulliObservationWeight p Omega) =
      ∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega := by
  classical
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Omega _
  by_cases hEvent : Event Omega
  · simp [hEvent]
  · simp [hEvent]

private lemma bernoulliExpectation_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) (hF : ∀ Omega, 0 ≤ F Omega) :
    0 ≤ bernoulliExpectation p F := by
  unfold bernoulliExpectation
  apply Finset.sum_nonneg
  intro Omega _
  exact mul_nonneg (bernoulliObservationWeight_nonneg hp hp_one Omega) (hF Omega)

private lemma bad_weight_mul_threshold_pow_le_expectation
    {n₁ n₂ : ℕ} {p threshold : ℝ} {q : ℕ}
    (hp : 0 ≤ p) (hp_one : p ≤ 1) (hthreshold : 0 ≤ threshold)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) (hF : ∀ Omega, 0 ≤ F Omega) :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        if F Omega ≤ threshold then 0 else bernoulliObservationWeight p Omega) *
        threshold ^ q ≤
      bernoulliExpectation p (fun Omega => F Omega ^ q) := by
  classical
  unfold bernoulliExpectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro Omega _
  by_cases hGood : F Omega ≤ threshold
  · simp [hGood]
    exact mul_nonneg (bernoulliObservationWeight_nonneg hp hp_one Omega)
      (pow_nonneg (hF Omega) q)
  · have hle : threshold ^ q ≤ F Omega ^ q := by
      exact pow_le_pow_left₀ hthreshold (le_of_not_ge hGood) q
    have hw : 0 ≤ bernoulliObservationWeight p Omega :=
      bernoulliObservationWeight_nonneg hp hp_one Omega
    simpa [hGood, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hle hw

private lemma bad_probability_eq_zero_of_zero_threshold
    {n₁ n₂ : ℕ} {p : ℝ} {q : ℕ}
    (hp : 0 ≤ p) (hp_one : p ≤ 1) (hq : 1 ≤ q)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) (hF : ∀ Omega, 0 ≤ F Omega)
    (hExp :
      bernoulliExpectation p (fun Omega => F Omega ^ q) = 0) :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        if F Omega ≤ 0 then 0 else bernoulliObservationWeight p Omega) = 0 := by
  classical
  have hq_pos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hterm_zero :
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega * F Omega ^ q = 0 := by
    have hsum :
        (∑ Omega : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Omega * F Omega ^ q) = 0 := by
      simpa [bernoulliExpectation] using hExp
    have hnonneg :
        ∀ Omega ∈ (Finset.univ : Finset (Finset (Fin n₁ × Fin n₂))),
          0 ≤ bernoulliObservationWeight p Omega * F Omega ^ q := by
      intro Omega _
      exact mul_nonneg (bernoulliObservationWeight_nonneg hp hp_one Omega)
        (pow_nonneg (hF Omega) q)
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp (by
        simpa using hsum)
    intro Omega
    exact hzero Omega (by simp)
  apply Finset.sum_eq_zero
  intro Omega _
  by_cases hGood : F Omega ≤ 0
  · simp [hGood]
  · have hF_pos : 0 < F Omega := lt_of_not_ge hGood
    have hpow_pos : 0 < F Omega ^ q := pow_pos hF_pos q
    have hw_zero : bernoulliObservationWeight p Omega = 0 := by
      have hz := hterm_zero Omega
      rcases mul_eq_zero.mp hz with hw | hpow
      · exact hw
      · exact False.elim ((ne_of_gt hpow_pos) hpow)
    simp [hGood, hw_zero]

theorem fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold :
    ∀ (β threshold : ℝ), 2 < β → 0 ≤ threshold →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          threshold ^ q * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X threshold) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro β threshold hβ hthreshold n₁ n₂ m q X hn₁ hn₂ hm hq hMoment
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let F : Finset (Fin n₁ × Fin n₂) → ℝ := fun Omega =>
    spectralNorm (centeredSamplingFluctuation Omega p X)
  let Good : Finset (Fin n₁ × Fin n₂) → Prop := fun Omega =>
    F Omega ≤ threshold
  let badProb : ℝ :=
    ∑ Omega : Finset (Fin n₁ × Fin n₂),
      if Good Omega then 0 else bernoulliObservationWeight p Omega
  let tail : ℝ := Real.rpow (↑(max n₁ n₂)) (-β)
  have hp_bounds := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hp : 0 ≤ p := by
    simpa [p] using hp_bounds.1
  have hp_one : p ≤ 1 := by
    simpa [p] using hp_bounds.2
  have hF_nonneg : ∀ Omega, 0 ≤ F Omega := by
    intro Omega
    exact spectralNorm_nonneg _
  have hMomentF :
      bernoulliExpectation p (fun Omega => F Omega ^ q) ≤
        threshold ^ q * tail := by
    simpa [p, F, tail] using hMoment
  have hmax_pos_nat : 0 < max n₁ n₂ := by
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have htail_nonneg : 0 ≤ tail := by
    exact Real.rpow_nonneg (Nat.cast_nonneg _) (-β)
  have hprob_add :
      bernoulliEventProb p Good + badProb = 1 := by
    have h :=
      bernoulliEventProb_add_compl (p := p) (n₁ := n₁) (n₂ := n₂) Good
    simpa [badProb, sum_bernoulliObservationWeight_eq_one hp hp_one] using h
  have hbad_le_tail : badProb ≤ tail := by
    by_cases hthreshold_pos : 0 < threshold
    · have hbad_mul_le :
          badProb * threshold ^ q ≤
            bernoulliExpectation p (fun Omega => F Omega ^ q) := by
        simpa [badProb, Good] using
          bad_weight_mul_threshold_pow_le_expectation
            (p := p) (threshold := threshold) (q := q)
            hp hp_one hthreshold F hF_nonneg
      have hmul_le : badProb * threshold ^ q ≤ tail * threshold ^ q := by
        have h := le_trans hbad_mul_le hMomentF
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      exact le_of_mul_le_mul_right hmul_le (pow_pos hthreshold_pos q)
    · have hthreshold_eq : threshold = 0 := by
        exact le_antisymm (le_of_not_gt hthreshold_pos) hthreshold
      have hq_pos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
      have hthreshold_pow_zero : threshold ^ q = 0 := by
        subst threshold
        cases q with
        | zero =>
            omega
        | succ q =>
            simp
      have hExp_nonneg :
          0 ≤ bernoulliExpectation p (fun Omega => F Omega ^ q) :=
        bernoulliExpectation_nonneg hp hp_one (fun Omega => F Omega ^ q)
          (fun Omega => pow_nonneg (hF_nonneg Omega) q)
      have hExp_le_zero :
          bernoulliExpectation p (fun Omega => F Omega ^ q) ≤ 0 := by
        simpa [hthreshold_pow_zero] using hMomentF
      have hExp_eq_zero :
          bernoulliExpectation p (fun Omega => F Omega ^ q) = 0 :=
        le_antisymm hExp_le_zero hExp_nonneg
      have hbad_zero :
          badProb = 0 := by
        have hzero :=
          bad_probability_eq_zero_of_zero_threshold
            (p := p) (q := q) hp hp_one hq F hF_nonneg hExp_eq_zero
        simpa [badProb, Good, hthreshold_eq] using hzero
      simpa [hbad_zero] using htail_nonneg
  have hgood :
      bernoulliEventProb p Good ≥ 1 - tail := by
    linarith
  simpa [p, F, Good, CenteredSamplingSpectralBound, tail, one_mul] using hgood

end MatrixCompletion.MatrixSamplingReuse_f22de60f
export MatrixCompletion.MatrixSamplingReuse_f22de60f (fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold)

/- Complete accepted-source reuse: theorem 997d56a7-0104-4ec9-b32c-c8d5a07c6534; submission 42ecdffb-5bfc-4df0-9092-09cc4ad6c79b.
Original SHA256 a4045953a76c094128c0a94bd90702bfb00aa327a68dcd1e81531d5f3348294d. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to fixed_matrix_centered_sampling_tail_from_log_moment_bound.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_997d56a7

open MatrixCompletion

private lemma entrySupNorm_nonneg_of_pos
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    0 ≤ entrySupNorm X := by
  let i0 : Fin n₁ := ⟨0, hn₁⟩
  let j0 : Fin n₂ := ⟨0, hn₂⟩
  exact le_trans (abs_nonneg (X i0 j0))
    (le_trans
      (le_ciSup
        (Finite.bddAbove_range (fun j : Fin n₂ => |X i0 j|)) j0)
      (le_ciSup
        (Finite.bddAbove_range
          (fun i : Fin n₁ => ⨆ j : Fin n₂, |X i j|)) i0))

/-- Repaired Markov/log-moment tail conversion.  The old reduction used a raw
Markov theorem without the required nonnegative-threshold hypothesis; here the
threshold is visibly nonnegative because it is a positive constant times a
square root times an entry sup norm. -/
theorem fixed_matrix_centered_sampling_tail_from_log_moment_bound
    (Cmoment : ℝ) :
    0 < Cmoment →
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        (∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                spectralNorm
                  (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
            (Cmoment * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) ^ q) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                (Ctail * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm X)) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCmoment
  rcases fixed_matrix_log_moment_scale_absorbs_markov_failure_factor
      Cmoment hCmoment with
    ⟨Ctail, hCtail, hAbsorb⟩
  refine ⟨Ctail, hCtail, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hSample hMoment
  rcases hMoment with ⟨q, hq, hqLog, hMomentBound⟩
  let threshold : ℝ :=
    Ctail * Real.sqrt
      ((β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂))) /
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
      entrySupNorm X
  have hThresholdNonneg : 0 ≤ threshold := by
    dsimp [threshold]
    exact mul_nonneg
      (mul_nonneg (le_of_lt hCtail) (Real.sqrt_nonneg _))
      (entrySupNorm_nonneg_of_pos X hn₁ hn₂)
  have hScaledMoment :
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        threshold ^ q *
          Real.rpow (↑(max n₁ n₂)) (-β) := by
    exact le_trans hMomentBound
      (by
        dsimp [threshold]
        exact hAbsorb β hβ n₁ n₂ m q X hn₁ hn₂ hm hq hqLog hSample)
  exact
    fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold
      β threshold hβ hThresholdNonneg n₁ n₂ m q X hn₁ hn₂ hm hq
      hScaledMoment

end MatrixCompletion.MatrixSamplingReuse_997d56a7
export MatrixCompletion.MatrixSamplingReuse_997d56a7 (fixed_matrix_centered_sampling_tail_from_log_moment_bound)

/- Complete accepted-source reuse: theorem 021320e3-9c3c-4c4f-8cfc-9ef039bcc516; submission c7bf86f8-d43d-4a11-b821-15ca98746c9d.
Original SHA256 87cc91e9ee131e0503f57fd1cad0cbf7e4c103a1fa3dd601496b90933d5d257c. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to fixed_matrix_centered_sampling_spectral_bound.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixSamplingReuse_021320e3

open MatrixCompletion

/-- Decompose Candes-Recht Theorem 6.3 into its log-moment estimate and the
Markov tail conversion. -/
theorem fixed_matrix_centered_sampling_spectral_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                (C * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm X)) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_log_moment_bound with
    ⟨Cmoment, hCmoment, hMoment⟩
  rcases fixed_matrix_centered_sampling_tail_from_log_moment_bound
      Cmoment hCmoment with
    ⟨Ctail, hCtail, hTail⟩
  refine ⟨Ctail, hCtail, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hSample
  exact hTail β hβ n₁ n₂ m X hn₁ hn₂ hm hSample
    (hMoment β hβ n₁ n₂ m X hn₁ hn₂ hm hSample)


end MatrixCompletion.MatrixSamplingReuse_021320e3
export MatrixCompletion.MatrixSamplingReuse_021320e3 (fixed_matrix_centered_sampling_spectral_bound)


/- Complete unchanged Round42 accepted component: SvdLeverage.lean; SHA256 d0afce6765032f7a3970d12f85ee70eb24ab340c4342e5b77b7cae363bae3546. -/

namespace MatrixThreshold

open MatrixCompletion
open scoped BigOperators

theorem sum_sq_orthonormal_combination {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (c : I -> Real) (v : I -> J -> Real)
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) :
    ∑ j, (∑ k, c k * v k j) ^ 2 = ∑ k, c k ^ 2 := by
  classical
  calc
    _ = ∑ k, ∑ l, c k * c l * (∑ j, v k j * v l j) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp [hv, pow_two]

theorem orthonormal_leverage_le_one {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (v : I -> J -> Real)
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) (i : J) :
    ∑ k, (v k i) ^ 2 <= 1 := by
  classical
  have h := sum_sq_orthonormal_combination (fun k => v k i) v hv
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => sq_nonneg (∑ k, v k i * v k j))
    (Finset.mem_univ i)
  rw [h] at hle
  simp only [← pow_two] at hle
  nlinarith [sq_nonneg ((∑ k, (v k i) ^ 2) - 1)]

theorem sign_row_sq_sum_eq_leverage {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) :
    ∑ j, (signMatrix S i j) ^ 2 = ∑ k, (S.u k i) ^ 2 := by
  simpa [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply] using
    sum_sq_orthonormal_combination (fun k => S.u k i) S.v S.v_orthonormal

theorem sign_column_sq_sum_eq_leverage {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (j : Fin n2) :
    ∑ i, (signMatrix S i j) ^ 2 = ∑ k, (S.v k j) ^ 2 := by
  simpa [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm] using
    sum_sq_orthonormal_combination (fun k => S.v k j) S.u S.u_orthonormal

theorem row_leverage_le_one {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) : ∑ k, (S.u k i) ^ 2 <= 1 :=
  orthonormal_leverage_le_one S.u S.u_orthonormal i

theorem column_leverage_le_one {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (j : Fin n2) : ∑ k, (S.v k j) ^ 2 <= 1 :=
  orthonormal_leverage_le_one S.v S.v_orthonormal j

theorem sign_sq_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hmu : 0 <= mu) (hA1 : A1 S mu)
    (i : Fin n1) (j : Fin n2) :
    (signMatrix S i j) ^ 2 <= mu ^ 2 * (r : Real) / ((n1 : Real) * (n2 : Real)) := by
  have h := sq_le_sq₀ (abs_nonneg (signMatrix S i j))
    (mul_nonneg hmu (Real.sqrt_nonneg ((r : Real) / ((n1 : Real) * (n2 : Real)))))
  have hs := h.mpr (hA1 i j)
  rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity)] at hs
  convert hs using 1
  ring

theorem row_leverage_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hmu : 0 <= mu) (hA1 : A1 S mu) (i : Fin n1) :
    ∑ k, (S.u k i) ^ 2 <= mu ^ 2 * (r : Real) / (n1 : Real) := by
  rw [← sign_row_sq_sum_eq_leverage S i]
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    sign_sq_le_of_A1 S mu hmu hA1 i j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1
  field_simp

theorem column_leverage_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hmu : 0 <= mu) (hA1 : A1 S mu) (j : Fin n2) :
    ∑ k, (S.v k j) ^ 2 <= mu ^ 2 * (r : Real) / (n2 : Real) := by
  rw [← sign_column_sq_sum_eq_leverage S j]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    sign_sq_le_of_A1 S mu hmu hA1 i j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1
  field_simp

end MatrixThreshold

/- Complete unchanged Round42 accepted component: ScalarThreshold.lean; SHA256 6ef08a8823e0d0657dd94e4c7970bf23b1e35b056049a77a720e3424114a9ea1. -/

namespace MatrixCompletion

theorem spectralNorm_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 <= spectralNorm X := norm_nonneg _

theorem spectralNorm_smul {n1 n2 : Nat} (c : Real) (X : RealMatrix n1 n2) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  simp [spectralNorm, map_smul, norm_smul, Real.norm_eq_abs]

theorem mul_sqrt_mul_sqrt_le_one (a x y : Real)
    (ha : 0 <= a) (hx : 0 <= x) (hy : 0 <= y)
    (h : a ^ 2 * x * y <= 1) :
    a * Real.sqrt x * Real.sqrt y <= 1 := by
  have hs : (a * Real.sqrt x * Real.sqrt y) ^ 2 = a ^ 2 * x * y := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
  have hn : 0 <= a * Real.sqrt x * Real.sqrt y := by positivity
  nlinarith

theorem scalar_threshold (mu N n r L p lam : Real)
    (hmu : 0 <= mu) (hN : 0 < N) (hn : 0 <= n) (hr : 0 <= r)
    (hL : 0 < L) (hp : 0 < p) (hlam : 1 <= lam)
    (hscale : lam * mu ^ 2 * n * r * L <= p * N) :
    p⁻¹ * Real.sqrt ((L * n) / p) *
        (2 * mu ^ 3 * Real.sqrt (r / N) * r * n / N) <=
      2 / (lam * L) := by
  have hlamp : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hpn : 0 < p * N := mul_pos hp hN
  have hlL : 0 < lam * L := mul_pos hlamp hL
  have hcoef : 0 <= mu ^ 2 * n * r * L := by positivity
  have hsmall : mu ^ 2 * n * r * L <= p * N := by
    have h := mul_nonneg (sub_nonneg.mpr hlam) hcoef
    nlinarith [hscale]
  have hsmall' : (mu ^ 2 * n * r * L) / (p * N) <= 1 := by
    apply (div_le_iff₀ hpn).2
    simpa using hsmall
  have heq : mu ^ 2 * (r / N) * ((L * n) / p) =
      (mu ^ 2 * n * r * L) / (p * N) := by
    field_simp
  have hunit : mu * Real.sqrt (r / N) * Real.sqrt ((L * n) / p) <= 1 := by
    apply mul_sqrt_mul_sqrt_le_one mu (r / N) ((L * n) / p) hmu
      (by positivity) (by positivity)
    simpa only [heq] using hsmall'
  have hbase : (mu ^ 2 * n * r) / (p * N) <= 1 / (lam * L) := by
    apply (div_le_div_iff₀ hpn hlL).2
    nlinarith [hscale]
  have hfactor : p⁻¹ * Real.sqrt ((L * n) / p) *
      (2 * mu ^ 3 * Real.sqrt (r / N) * r * n / N) =
      (2 * ((mu ^ 2 * n * r) / (p * N))) *
        (mu * Real.sqrt (r / N) * Real.sqrt ((L * n) / p)) := by
    field_simp
  rw [hfactor]
  calc
    (2 * ((mu ^ 2 * n * r) / (p * N))) *
        (mu * Real.sqrt (r / N) * Real.sqrt ((L * n) / p)) <=
        (2 * ((mu ^ 2 * n * r) / (p * N))) * 1 :=
      mul_le_mul_of_nonneg_left hunit (by positivity)
    _ <= 2 / (lam * L) := by
      convert mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : Real) <= 2) using 1 <;> ring

end MatrixCompletion

/- Complete unchanged Round42 accepted component: TangentDiagonalBound.lean; SHA256 255b655e54ca6317f60411075a5ca8380fd94644ab57adf78fc0503b47b5528b. -/

namespace MatrixThreshold

open MatrixCompletion
open scoped BigOperators

theorem matrixInner_coordinateMatrix {n1 n2 : Nat}
    (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  classical
  simp [matrixInner, coordinateMatrix, ite_and]

theorem tangentCoordinateKernel_diagonal {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (i : Fin n1) (j : Fin n2) :
    tangentCoordinateKernel S i j i j =
      (∑ k, (S.u k i) ^ 2) + (∑ k, (S.v k j) ^ 2) -
        (∑ k, (S.u k i) ^ 2) * (∑ k, (S.v k j) ^ 2) := by
  classical
  rw [tangentCoordinateKernel, matrixInner_coordinateMatrix]
  simp [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection, coordinateMatrix, ite_and, pow_two,
    Finset.sum_mul]

theorem tangentCoordinateKernel_diagonal_abs_le {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (i : Fin n1) (j : Fin n2) :
    |tangentCoordinateKernel S i j i j| <=
      (∑ k, (S.u k i) ^ 2) + (∑ k, (S.v k j) ^ 2) := by
  have hu0 : 0 <= ∑ k, (S.u k i) ^ 2 := Finset.sum_nonneg (by intros; positivity)
  have hv0 : 0 <= ∑ k, (S.v k j) ^ 2 := Finset.sum_nonneg (by intros; positivity)
  have hv1 := column_leverage_le_one S j
  rw [tangentCoordinateKernel_diagonal]
  have hnonneg : 0 <= (∑ k, (S.u k i) ^ 2) + (∑ k, (S.v k j) ^ 2) -
      (∑ k, (S.u k i) ^ 2) * (∑ k, (S.v k j) ^ 2) := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hv1)]
  rw [abs_of_nonneg hnonneg]
  nlinarith [mul_nonneg hu0 hv0]

theorem diagonal_base_entrySupNorm_le_sum {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (mu : Real)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (hmu : 0 <= mu) (hA1 : A1 S mu) :
    entrySupNorm (linearNeumannDiagonalBaseMatrix S) <=
      mu ^ 3 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real))) *
        (r : Real) * ((n1 : Real) + (n2 : Real)) / ((n1 : Real) * (n2 : Real)) := by
  haveI : Nonempty (Fin n1) := ⟨⟨0, hn1⟩⟩
  haveI : Nonempty (Fin n2) := ⟨⟨0, hn2⟩⟩
  have hn1r : (n1 : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn1)
  have hn2r : (n2 : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn2)
  unfold entrySupNorm
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  have hkernel : |tangentCoordinateKernel S i j i j| <=
      mu ^ 2 * (r : Real) / (n1 : Real) + mu ^ 2 * (r : Real) / (n2 : Real) :=
    (tangentCoordinateKernel_diagonal_abs_le S i j).trans
      (add_le_add (row_leverage_le_of_A1 S mu hn1 hn2 hmu hA1 i)
        (column_leverage_le_of_A1 S mu hn1 hn2 hmu hA1 j))
  change |signMatrix S i j * tangentCoordinateKernel S i j i j| <= _
  rw [abs_mul]
  calc
    |signMatrix S i j| * |tangentCoordinateKernel S i j i j| <=
        (mu * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real)))) *
          (mu ^ 2 * (r : Real) / (n1 : Real) + mu ^ 2 * (r : Real) / (n2 : Real)) :=
      mul_le_mul (hA1 i j) hkernel (abs_nonneg _)
        (mul_nonneg hmu (Real.sqrt_nonneg _))
    _ = _ := by field_simp [hn1r, hn2r]; ring

theorem diagonal_base_entrySupNorm_le {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (mu : Real)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (hmu : 0 <= mu) (hA1 : A1 S mu) :
    entrySupNorm (linearNeumannDiagonalBaseMatrix S) <=
      2 * mu ^ 3 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real))) *
        (r : Real) * (max n1 n2 : Nat) / ((n1 : Real) * (n2 : Real)) := by
  have h1 : (n1 : Real) <= (max n1 n2 : Nat) := by exact_mod_cast (Nat.le_max_left n1 n2)
  have h2 : (n2 : Real) <= (max n1 n2 : Nat) := by exact_mod_cast (Nat.le_max_right n1 n2)
  have hsum : (n1 : Real) + (n2 : Real) <= 2 * (max n1 n2 : Nat) := by linarith
  refine (diagonal_base_entrySupNorm_le_sum S mu hn1 hn2 hmu hA1).trans ?_
  have hcoef : 0 <= mu ^ 3 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real))) *
      (r : Real) := by positivity
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hcoef)
    (show 0 <= (n1 : Real) * (n2 : Real) by positivity)
  convert h using 1
  ring

end MatrixThreshold

/- Explicitly strengthened complete Round42 conclusion, removing only unused base-bound hypotheses: DeterministicThreshold.lean; SHA256 86850ed0d5c6171df88c1b618e3fafb0982350842d76fcf9d6460e44b8d54576. -/

open MatrixCompletion

/- Complete adaptation of Round42 Conclusion.lean (SHA256
6947c723de80e5d2097bba8421982b2390d539b3b5994c930cc34f409c489fb3).
The proof was authored by solver_resume using the credited complete Round42 components.
This strengthening changes the declaration name and removes only the unused Cbase
parameter, its positivity premise, and its supplied base-bound premise, together
with the corresponding intro binders. Every other proof line is retained. -/

set_option linter.unusedVariables false in
theorem MatrixThreshold.deterministic_threshold
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        linearNeumannDiagonalCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
              (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (linearNeumannDiagonalBaseMatrix S) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (linearNeumannDiagonalBaseMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (linearNeumannDiagonalBaseMatrix S)) →
        spectralNorm
            (linearNeumannDiagonalCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cthreshold * Real.rpow lam (-1) := by
  intro hfixed
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * Cfixed / Real.log 2, by positivity, ?_⟩
  intro β lam hβ hlam n1 n2 r m M mu0 mu S hn1 hn2 hr hm hmu0 hmu hA0 hA1
    hsample Omega hrepr hspectral
  let N : Real := (n1 : Real) * (n2 : Real)
  let n : Real := (max n1 n2 : Nat)
  let L : Real := β * Real.log n
  let p : Real := (m : Real) / N
  have hN : 0 < N := mul_pos (Nat.cast_pos.mpr hn1) (Nat.cast_pos.mpr hn2)
  have hp0 : 0 <= p := div_nonneg (Nat.cast_nonneg _) hN.le
  have hp1 : p <= 1 := (div_le_one hN).mpr (by dsimp [N]; exact_mod_cast hm)
  have hlamp : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hmu' : 0 <= mu := le_trans zero_le_one hmu
  have hrepr' : linearNeumannDiagonalCenteredContribution Omega S p =
      (p⁻¹ * (1 - 2 * p)) •
        centeredSamplingFluctuation Omega p (linearNeumannDiagonalBaseMatrix S) := hrepr
  change spectralNorm (linearNeumannDiagonalCenteredContribution Omega S p) <= _
  by_cases hpzero : p = 0
  · rw [hrepr', MatrixCompletion.spectralNorm_smul, hpzero]
    simp only [inv_zero, zero_mul, abs_zero]
    rw [Real.rpow_eq_pow, Real.rpow_neg_one]
    positivity
  have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpzero)
  by_cases hnmax : max n1 n2 = 1
  · have hzero : spectralNorm
        (centeredSamplingFluctuation Omega p (linearNeumannDiagonalBaseMatrix S)) = 0 := by
      apply le_antisymm
      · simpa [CenteredSamplingSpectralBound, hnmax, p, N] using hspectral
      · exact MatrixCompletion.spectralNorm_nonneg _
    rw [hrepr', MatrixCompletion.spectralNorm_smul, hzero, mul_zero]
    rw [Real.rpow_eq_pow, Real.rpow_neg_one]
    positivity
  have hnmax2 : 2 <= max n1 n2 := by
    have := Nat.le_max_left n1 n2
    omega
  have hn2r : (2 : Real) <= n := by dsimp [n]; exact_mod_cast hnmax2
  have hlog : Real.log 2 <= Real.log n := Real.log_le_log (by norm_num) hn2r
  have hlogn : 0 < Real.log n := lt_of_lt_of_le hlog2 hlog
  have hL : 0 < L := mul_pos (by linarith) hlogn
  have hLlower : Real.log 2 <= L := by
    dsimp [L]
    nlinarith [mul_nonneg (show 0 <= β - 1 by linarith) hlogn.le]
  have hscale : lam * mu ^ 2 * n * (r : Real) * L <= p * N := by
    have hsample' : lam * mu * max (Real.sqrt mu0) mu * n * (r : Real) * L <=
        (m : Real) := hsample
    have hpN : p * N = (m : Real) := by dsimp [p]; field_simp
    rw [hpN]
    calc
      lam * mu ^ 2 * n * (r : Real) * L = lam * mu * mu * n * (r : Real) * L := by ring
      _ <= lam * mu * max (Real.sqrt mu0) mu * n * (r : Real) * L := by
        gcongr
        exact le_max_right _ _
      _ <= _ := hsample'
  have hcenter : spectralNorm
      (centeredSamplingFluctuation Omega p (linearNeumannDiagonalBaseMatrix S)) <=
      Cfixed * Real.sqrt ((L * n) / p) * entrySupNorm (linearNeumannDiagonalBaseMatrix S) := by
    have hLn : L * n = β * n * Real.log n := by dsimp [L]; ring
    rw [hLn]
    exact hspectral
  have hcoef : |p⁻¹ * (1 - 2 * p)| <= p⁻¹ := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hp0)]
    have hfactor : |1 - 2 * p| <= 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    simpa using mul_le_mul_of_nonneg_left hfactor (inv_nonneg.mpr hp0)
  have hbase' := MatrixThreshold.diagonal_base_entrySupNorm_le S mu hn1 hn2 hmu' hA1
  change entrySupNorm (linearNeumannDiagonalBaseMatrix S) <=
    2 * mu ^ 3 * Real.sqrt ((r : Real) / N) * (r : Real) * n / N at hbase'
  have hscalar := scalar_threshold mu N n (r : Real) L p lam hmu' hN
    (by positivity) (Nat.cast_nonneg _) hL hp hlam hscale
  calc
    spectralNorm (linearNeumannDiagonalCenteredContribution Omega S p) =
        |p⁻¹ * (1 - 2 * p)| * spectralNorm
          (centeredSamplingFluctuation Omega p (linearNeumannDiagonalBaseMatrix S)) := by
      rw [hrepr', MatrixCompletion.spectralNorm_smul]
    _ <= p⁻¹ * spectralNorm
        (centeredSamplingFluctuation Omega p (linearNeumannDiagonalBaseMatrix S)) :=
      mul_le_mul_of_nonneg_right hcoef (MatrixCompletion.spectralNorm_nonneg _)
    _ <= p⁻¹ * (Cfixed * Real.sqrt ((L * n) / p) *
        entrySupNorm (linearNeumannDiagonalBaseMatrix S)) :=
      mul_le_mul_of_nonneg_left hcenter (inv_nonneg.mpr hp0)
    _ <= p⁻¹ * (Cfixed * Real.sqrt ((L * n) / p) *
        (2 * mu ^ 3 * Real.sqrt ((r : Real) / N) * (r : Real) * n / N)) := by
      gcongr
    _ = Cfixed * (p⁻¹ * Real.sqrt ((L * n) / p) *
        (2 * mu ^ 3 * Real.sqrt ((r : Real) / N) * (r : Real) * n / N)) := by ring
    _ <= Cfixed * (2 / (lam * L)) := mul_le_mul_of_nonneg_left hscalar hfixed.le
    _ <= Cfixed * (2 / (lam * Real.log 2)) := by
      apply mul_le_mul_of_nonneg_left _ hfixed.le
      exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hlamp hlog2)
        (mul_le_mul_of_nonneg_left hLlower hlamp.le)
    _ = (2 * Cfixed / Real.log 2) * Real.rpow lam (-1) := by
      rw [Real.rpow_eq_pow, Real.rpow_neg_one]
      ring

/- New exact probability conclusion: Conclusion.lean; SHA256 c7aafa4376cc2a24f98dc7718cd2f136f1e9619c76862d6eb8ba5c80564ff558. -/

open MatrixCompletion

theorem solution :
    ∃ Ccenter ccenter : ℝ, 0 < Ccenter ∧ 0 < ccenter ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannDiagonalCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Ccenter * Real.rpow lam (-1)) ≥
          1 - ccenter * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_spectral_bound with
    ⟨Cfixed, hfixed, hsampling⟩
  rcases MatrixThreshold.deterministic_threshold Cfixed hfixed with
    ⟨Ccenter, hcenter, hthreshold⟩
  refine ⟨Ccenter, 1, hcenter, by norm_num, ?_⟩
  intro β lam hβ hlam n1 n2 r m M mu0 mu1 S hn1 hn2 hr hm hmu0 hmu1 hA0 hA1
    hsample
  have hlower := linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
    β lam n1 n2 r m mu0 mu1 hβ hlam hn1 hn2 hr hmu0 hmu1 hsample
  have hprob := hsampling β hβ n1 n2 m (linearNeumannDiagonalBaseMatrix S)
    hn1 hn2 hm hlower
  have hp := sample_ratio_between_zero_and_one n1 n2 m hn1 hn2 hm
  apply le_trans hprob
  apply bernoulli_event_probability_mono _ _ _ hp.1 hp.2
  intro Omega hspectral
  exact hthreshold β lam hβ hlam n1 n2 r m M mu0 mu1 S hn1 hn2 hr hm hmu0 hmu1
    hA0 hA1 hsample Omega
    (linear_neumann_diagonal_centered_as_fixed_matrix_fluctuation Omega S _)
    hspectral

