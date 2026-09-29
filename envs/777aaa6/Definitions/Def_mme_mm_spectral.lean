-- Prove2me | Definitions.Def_mme_mm_spectral
-- name    : mme_mm_spectral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T17:06:59.351943+00:00
-- url     : https://prove2.me/theorems/55acf53a-ebab-48c1-aaf5-fb12e6048c0f
-- statement:
--   **Abstract matrix-multiplication spectral evaluation and the asymptotic sum inequality.**
--
--   The abstract τ-theorem on top of an arbitrary Strassen preorder $P$ on a commutative semiring $R$ equipped with a family of "matrix-multiplication elements" $\mathrm{MMel}_R(n, m, p) \in R$ satisfying the standard structural laws.
--
--   **The `MMData` bundle.** `MMData R P` bundles:
--   - $\mathrm{MMel} : \mathbb{N}^3 \to R$ — the family of MM elements;
--   - multiplicativity: $\mathrm{MMel}(n, m, p) \cdot \mathrm{MMel}(n', m', p') \sim_P \mathrm{MMel}(nn', mm', pp')$;
--   - monotonicity in each dimension: $n \leq n' \Rightarrow \mathrm{MMel}(n, m, p) \leq_P \mathrm{MMel}(n', m, p)$ etc.;
--   - trivial bounds: $\mathrm{MMel}(n, m, p) \leq_P n m p$ (one rank-1 summand per index);
--   - `cyclic`: for every spectrum point $\varphi$, there is another $\varphi'$ with $\varphi'(\mathrm{MMel}(n, m, p)) = \varphi(\mathrm{MMel}(p, n, m))$ (the permutation symmetry).
--
--   **Coordinate exponents and `MM_eval`.** Using the Erdős–Hewitt lemma (`Def_mme_jensen`), each spectrum point $\varphi$ factors through three coordinate exponents $\theta_1, \theta_2, \theta_3 : \mathrm{Spec}(P) \to \mathbb{R}$ such that
--   $$\varphi(\mathrm{MMel}_R(n, m, p)) \;=\; n^{\theta_1(\varphi)} \, m^{\theta_2(\varphi)} \, p^{\theta_3(\varphi)}.$$
--   Continuity of $\theta_j$ follows from continuity of $\varphi$ at $\mathrm{MMel}(n, m, p)$ for each fixed $(n, m, p)$.
--
--   **The abstract asymptotic sum inequality.** `MMData.sum_inequality`: if $\mathrm{asymptoticRank}_P(\sum_i \mathrm{MMel}(n_i, m_i, p_i)) \leq r$, then
--   $$\sum_i (n_i m_i p_i)^{\omega_{\mathrm{abs}}/3} \;\leq\; r, \qquad \omega_{\mathrm{abs}} = \sup_\varphi (\theta_1 + \theta_2 + \theta_3)(\varphi).$$
--   The proof combines spectrum-point evaluation, the cyclic symmetry, and Jensen-on-$S_3$ to collapse three distinct exponents into the symmetric $\omega/3$. Sorry-free *modulo* the three deep spectrum leaves (provided by `Def_mme_spectrum` / `Def_mme_duality`) and the structural MM hypotheses (supplied at the concrete level by `Def_mme_tensor_bridge`).
-- source:
--   https://github.com/EntropyIncreaser/Prism

import Definitions.Def_mme_duality
import Definitions.Def_mme_jensen

/-! # Abstract matrix-multiplication spectral evaluation and sum inequality (MME)

Given an abstract Strassen preorder `P` on a commutative semiring `R` together with a
family `MMel n m p : R` of "matrix-multiplication elements" satisfying the standard
structural laws (multiplicativity, monotonicity, the trivial bounds), we develop:

* `θ₁ θ₂ θ₃ : AsymptoticSpectrumPoint → ℝ` and `MM_eval`
  (`φ(MMel n m p) = n^θ₁ m^θ₂ p^θ₃`) via the Erdős–Hewitt lemma;
* the abstract **asymptotic sum inequality**
  `asymptoticRank P (∑ MMel nᵢ mᵢ pᵢ) ≤ r ⟹ ∑ (nᵢmᵢpᵢ)^(ωabs/3) ≤ r`,
  where `ωabs = ⨆_φ (θ₁+θ₂+θ₃)`.

All of this is sorry-free *modulo* the three deep spectrum leaves
(`tends_to_asymptoticRank`, `AsymptoticSpectrumPoint.nonempty`,
`asymptoticRank_eq_sup_spectrum`) and the structural MM hypotheses, which the concrete
tensor instantiation (`Def_mme_tensor_bridge`) supplies.

The structural MM hypotheses are bundled as `MMData R P`. The permutation symmetry of
the spectrum is captured by `MMData.cyclic`: for each spectrum point there is another
realizing the cyclic relabelling of `(n,m,p)`. -/

universe u

open MME BigOperators Filter Topology

namespace MME

/-- Bundle of the structural facts about a matrix-multiplication element family `MMel`
inside a Strassen preorder `P`, sufficient to run the asymptotic-spectrum argument. -/
structure MMData (R : Type u) [CommSemiring R] (P : StrassenPreorder R) where
  /-- The matrix-multiplication elements `⟨n,m,p⟩`. -/
  MMel : ℕ → ℕ → ℕ → R
  /-- `⟨1,1,1⟩ = 1`. -/
  one : MMel 1 1 1 = 1
  /-- Multiplicativity: `⟨n,m,p⟩ · ⟨n',m',p'⟩ = ⟨nn',mm',pp'⟩`. -/
  mul : ∀ n m p n' m' p' : ℕ,
    MMel n m p * MMel n' m' p' = MMel (n * n') (m * m') (p * p')
  /-- Monotonicity in all three dimensions. -/
  le_of_le : ∀ {n n' m m' p p' : ℕ}, n ≤ n' → m ≤ m' → p ≤ p' →
    P.le (MMel n m p) (MMel n' m' p')
  /-- Trivial upper bound `⟨n,m,p⟩ ≤ n·m·p`. -/
  le_mul : ∀ n m p : ℕ, P.le (MMel n m p) ((n * m * p : ℕ) : R)
  /-- Nonvanishing for positive dimensions. -/
  ne_zero : ∀ {n m p : ℕ}, 1 ≤ n → 1 ≤ m → 1 ≤ p → MMel n m p ≠ 0
  /-- Cyclic symmetry of the spectrum: for every spectrum point `φ` there is a spectrum
  point `φ'` with `φ'(⟨n,m,p⟩) = φ(⟨p,n,m⟩)` for all `n,m,p`. -/
  cyclic : ∀ φ : AsymptoticSpectrumPoint R P, ∃ φ' : AsymptoticSpectrumPoint R P,
    ∀ n m p : ℕ, φ' (MMel n m p) = φ (MMel p n m)

namespace MMData

variable {R : Type u} [CommSemiring R] {P : StrassenPreorder R} (D : MMData R P)

/-- `MMel n m p ≥ 1` for positive dimensions. -/
theorem one_le (n m p : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    P.le 1 (D.MMel n m p) := by
  have h := D.le_of_le hn hm hp
  rwa [D.one] at h

/-- `1 ≤ φ(MMel n m p)` for positive dimensions. -/
theorem one_le_phi (φ : AsymptoticSpectrumPoint R P) {n m p : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) : 1 ≤ φ (D.MMel n m p) := by
  have := φ.monotone' (D.one_le n m p hn hm hp)
  rwa [map_one] at this

/-- `φ(MMel n m p) ≤ n·m·p`. -/
theorem phi_le_mul (φ : AsymptoticSpectrumPoint R P) (n m p : ℕ) :
    φ (D.MMel n m p) ≤ (n * m * p : ℕ) := by
  have := φ.monotone' (D.le_mul n m p)
  rwa [map_natCast] at this

theorem phi_pos (φ : AsymptoticSpectrumPoint R P) {n m p : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) : 0 < φ (D.MMel n m p) :=
  lt_of_lt_of_le zero_lt_one (D.one_le_phi φ hn hm hp)

/-! ## The exponent parameters θ₁, θ₂, θ₃ -/

/-- `θ₁(φ) = log φ(⟨2,1,1⟩) / log 2`. -/
noncomputable def θ₁ (φ : AsymptoticSpectrumPoint R P) : ℝ :=
  Real.log (φ (D.MMel 2 1 1)) / Real.log 2

/-- `θ₂(φ) = log φ(⟨1,2,1⟩) / log 2`. -/
noncomputable def θ₂ (φ : AsymptoticSpectrumPoint R P) : ℝ :=
  Real.log (φ (D.MMel 1 2 1)) / Real.log 2

/-- `θ₃(φ) = log φ(⟨1,1,2⟩) / log 2`. -/
noncomputable def θ₃ (φ : AsymptoticSpectrumPoint R P) : ℝ :=
  Real.log (φ (D.MMel 1 1 2)) / Real.log 2

/-- **MM evaluation:** every spectrum point is a product power
`φ(⟨n,m,p⟩) = n^θ₁ · m^θ₂ · p^θ₃`. -/
theorem MM_eval (φ : AsymptoticSpectrumPoint R P) {n m p : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    φ (D.MMel n m p) = (n : ℝ) ^ D.θ₁ φ * (m : ℝ) ^ D.θ₂ φ * (p : ℝ) ^ D.θ₃ φ := by
  let f₁ : ℕ → ℝ := fun a => φ (D.MMel a 1 1)
  let f₂ : ℕ → ℝ := fun a => φ (D.MMel 1 a 1)
  let f₃ : ℕ → ℝ := fun a => φ (D.MMel 1 1 a)
  have h_mul₁ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f₁ (a * b) = f₁ a * f₁ b := by
    intro a b _ _
    show φ (D.MMel (a * b) 1 1) = φ (D.MMel a 1 1) * φ (D.MMel b 1 1)
    rw [← map_mul, D.mul a 1 1 b 1 1]
  have h_mul₂ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f₂ (a * b) = f₂ a * f₂ b := by
    intro a b _ _
    show φ (D.MMel 1 (a * b) 1) = φ (D.MMel 1 a 1) * φ (D.MMel 1 b 1)
    rw [← map_mul, D.mul 1 a 1 1 b 1]
  have h_mul₃ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f₃ (a * b) = f₃ a * f₃ b := by
    intro a b _ _
    show φ (D.MMel 1 1 (a * b)) = φ (D.MMel 1 1 a) * φ (D.MMel 1 1 b)
    rw [← map_mul, D.mul 1 1 a 1 1 b]
  have h_one₁ : f₁ 1 = 1 := by show φ (D.MMel 1 1 1) = 1; rw [D.one]; exact map_one _
  have h_one₂ : f₂ 1 = 1 := by show φ (D.MMel 1 1 1) = 1; rw [D.one]; exact map_one _
  have h_one₃ : f₃ 1 = 1 := by show φ (D.MMel 1 1 1) = 1; rw [D.one]; exact map_one _
  have h_mono₁ : ∀ a b : ℕ, 1 ≤ a → a ≤ b → f₁ a ≤ f₁ b := fun a b _ hab =>
    φ.monotone' (D.le_of_le hab (le_refl _) (le_refl _))
  have h_mono₂ : ∀ a b : ℕ, 1 ≤ a → a ≤ b → f₂ a ≤ f₂ b := fun a b _ hab =>
    φ.monotone' (D.le_of_le (le_refl _) hab (le_refl _))
  have h_mono₃ : ∀ a b : ℕ, 1 ≤ a → a ≤ b → f₃ a ≤ f₃ b := fun a b _ hab =>
    φ.monotone' (D.le_of_le (le_refl _) (le_refl _) hab)
  have h_one_le₁ : ∀ a : ℕ, 1 ≤ a → 1 ≤ f₁ a := fun a ha =>
    D.one_le_phi φ ha (le_refl _) (le_refl _)
  have h_one_le₂ : ∀ a : ℕ, 1 ≤ a → 1 ≤ f₂ a := fun a ha =>
    D.one_le_phi φ (le_refl _) ha (le_refl _)
  have h_one_le₃ : ∀ a : ℕ, 1 ≤ a → 1 ≤ f₃ a := fun a ha =>
    D.one_le_phi φ (le_refl _) (le_refl _) ha
  have h_le_n₁ : ∀ a : ℕ, 1 ≤ a → f₁ a ≤ a := by
    intro a _; have h := D.phi_le_mul φ a 1 1
    rwa [show ((a * 1 * 1 : ℕ) : ℝ) = a by push_cast; ring] at h
  have h_le_n₂ : ∀ a : ℕ, 1 ≤ a → f₂ a ≤ a := by
    intro a _; have h := D.phi_le_mul φ 1 a 1
    rwa [show ((1 * a * 1 : ℕ) : ℝ) = a by push_cast; ring] at h
  have h_le_n₃ : ∀ a : ℕ, 1 ≤ a → f₃ a ≤ a := by
    intro a _; have h := D.phi_le_mul φ 1 1 a
    rwa [show ((1 * 1 * a : ℕ) : ℝ) = a by push_cast; ring] at h
  have hf₁_eq := mono_mult_eq_rpow f₁ h_mul₁ h_one₁ h_mono₁ h_one_le₁ h_le_n₁
  have hf₂_eq := mono_mult_eq_rpow f₂ h_mul₂ h_one₂ h_mono₂ h_one_le₂ h_le_n₂
  have hf₃_eq := mono_mult_eq_rpow f₃ h_mul₃ h_one₃ h_mono₃ h_one_le₃ h_le_n₃
  have hMM_decomp : D.MMel n m p = D.MMel n 1 1 * D.MMel 1 m 1 * D.MMel 1 1 p := by
    have e1 : D.MMel n 1 1 * D.MMel 1 m 1 = D.MMel n m 1 := by
      rw [D.mul n 1 1 1 m 1]; norm_num
    have e2 : D.MMel n m 1 * D.MMel 1 1 p = D.MMel n m p := by
      rw [D.mul n m 1 1 1 p]; norm_num
    rw [e1, e2]
  rw [hMM_decomp, map_mul, map_mul]
  show f₁ n * f₂ m * f₃ p = _
  rw [hf₁_eq n hn, hf₂_eq m hm, hf₃_eq p hp]
  rfl

/-! ## θ bounds -/

theorem θ₁_nonneg (φ : AsymptoticSpectrumPoint R P) : 0 ≤ D.θ₁ φ :=
  div_nonneg (Real.log_nonneg (D.one_le_phi φ (by norm_num) (by norm_num) (by norm_num)))
    (Real.log_nonneg (by norm_num))

theorem θ₂_nonneg (φ : AsymptoticSpectrumPoint R P) : 0 ≤ D.θ₂ φ :=
  div_nonneg (Real.log_nonneg (D.one_le_phi φ (by norm_num) (by norm_num) (by norm_num)))
    (Real.log_nonneg (by norm_num))

theorem θ₃_nonneg (φ : AsymptoticSpectrumPoint R P) : 0 ≤ D.θ₃ φ :=
  div_nonneg (Real.log_nonneg (D.one_le_phi φ (by norm_num) (by norm_num) (by norm_num)))
    (Real.log_nonneg (by norm_num))

/-! ## Continuity of θ -/

theorem continuous_θ₁ : Continuous (fun φ : AsymptoticSpectrumPoint R P => D.θ₁ φ) := by
  refine Continuous.div_const ?_ _
  exact Real.continuousOn_log.comp_continuous (AsymptoticSpectrumPoint.continuous_eval _)
    (fun φ => ne_of_gt (D.phi_pos φ (by norm_num) (by norm_num) (by norm_num)))

theorem continuous_θ₂ : Continuous (fun φ : AsymptoticSpectrumPoint R P => D.θ₂ φ) := by
  refine Continuous.div_const ?_ _
  exact Real.continuousOn_log.comp_continuous (AsymptoticSpectrumPoint.continuous_eval _)
    (fun φ => ne_of_gt (D.phi_pos φ (by norm_num) (by norm_num) (by norm_num)))

theorem continuous_θ₃ : Continuous (fun φ : AsymptoticSpectrumPoint R P => D.θ₃ φ) := by
  refine Continuous.div_const ?_ _
  exact Real.continuousOn_log.comp_continuous (AsymptoticSpectrumPoint.continuous_eval _)
    (fun φ => ne_of_gt (D.phi_pos φ (by norm_num) (by norm_num) (by norm_num)))

theorem continuous_θsum :
    Continuous (fun φ : AsymptoticSpectrumPoint R P => D.θ₁ φ + D.θ₂ φ + D.θ₃ φ) :=
  (D.continuous_θ₁.add D.continuous_θ₂).add D.continuous_θ₃

/-! ## The abstract MM exponent and the sum inequality -/

/-- The abstract MM exponent `ωabs = ⨆_φ (θ₁ + θ₂ + θ₃)(φ)`. -/
noncomputable def omegaAbs : ℝ :=
  ⨆ φ : AsymptoticSpectrumPoint R P, D.θ₁ φ + D.θ₂ φ + D.θ₃ φ

/-- The cyclic relation transfers `θ`: if `φ'(⟨n,m,p⟩) = φ(⟨p,n,m⟩)` then
`θ₁(φ') = θ₂(φ)`, `θ₂(φ') = θ₃(φ)`, `θ₃(φ') = θ₁(φ)`. -/
theorem theta_cyclic {φ φ' : AsymptoticSpectrumPoint R P}
    (h : ∀ n m p : ℕ, φ' (D.MMel n m p) = φ (D.MMel p n m)) :
    D.θ₁ φ' = D.θ₂ φ ∧ D.θ₂ φ' = D.θ₃ φ ∧ D.θ₃ φ' = D.θ₁ φ := by
  refine ⟨?_, ?_, ?_⟩
  · unfold θ₁ θ₂; rw [h 2 1 1]
  · unfold θ₂ θ₃; rw [h 1 2 1]
  · unfold θ₃ θ₁; rw [h 1 1 2]

/-- **Abstract asymptotic sum inequality.** If the asymptotic rank of the sum of MM
elements is at most `r`, then `∑ᵢ (nᵢ·mᵢ·pᵢ)^(ωabs/3) ≤ r`. -/
theorem sum_inequality {ι : Type*} [Fintype ι]
    (n m p : ι → ℕ) (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i)
    (r : ℕ)
    (h : StrassenPreorder.asymptoticRank P (∑ i, D.MMel (n i) (m i) (p i)) ≤ r) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (D.omegaAbs / 3) ≤ r := by
  -- Step 1: every spectrum point sends the sum to ≤ r.
  have hspec : ∀ φ : AsymptoticSpectrumPoint R P,
      ∑ i, φ (D.MMel (n i) (m i) (p i)) ≤ r := by
    intro φ
    have h_le_AR := StrassenPreorder.eval_le_asymptoticRank P
      (∑ i, D.MMel (n i) (m i) (p i)) φ
    have hphi : φ (∑ i, D.MMel (n i) (m i) (p i)) ≤ (r : ℝ) :=
      le_trans h_le_AR (by exact_mod_cast h)
    rwa [map_sum] at hphi
  -- Step 2: rewrite each via MM_eval.
  have htheta : ∀ φ : AsymptoticSpectrumPoint R P,
      ∑ i, (n i : ℝ) ^ D.θ₁ φ * (m i : ℝ) ^ D.θ₂ φ * (p i : ℝ) ^ D.θ₃ φ ≤ r := by
    intro φ
    rw [show (∑ i, (n i : ℝ) ^ D.θ₁ φ * (m i : ℝ) ^ D.θ₂ φ * (p i : ℝ) ^ D.θ₃ φ) =
        ∑ i, φ (D.MMel (n i) (m i) (p i)) from
      Finset.sum_congr rfl fun i _ => (D.MM_eval φ (hn i) (hm i) (hp i)).symm]
    exact hspec φ
  have hn_pos : ∀ i, (0 : ℝ) < (n i : ℝ) := fun i => by
    have h1 : (1 : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hn i
    linarith
  have hm_pos : ∀ i, (0 : ℝ) < (m i : ℝ) := fun i => by
    have h1 : (1 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm i
    linarith
  have hp_pos : ∀ i, (0 : ℝ) < (p i : ℝ) := fun i => by
    have h1 : (1 : ℝ) ≤ (p i : ℝ) := by exact_mod_cast hp i
    linarith
  set F : ℝ × ℝ × ℝ → ℝ :=
    fun v => ∑ i, (n i : ℝ) ^ v.1 * (m i : ℝ) ^ v.2.1 * (p i : ℝ) ^ v.2.2 with hF
  have hF_convex : ConvexOn ℝ Set.univ F :=
    sum_rpow_convex (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) (fun i => (p i : ℝ))
      hn_pos hm_pos hp_pos
  -- Step 3: the three cyclic permutations of θ each give ≤ r.
  have hF_perm : ∀ φ : AsymptoticSpectrumPoint R P,
      ∀ σ ∈ ({Equiv.refl _, cyclicPerm3, cyclicPerm3 * cyclicPerm3} :
          Set (Equiv.Perm (Fin 3))),
        F (permuteTriple σ (D.θ₁ φ, D.θ₂ φ, D.θ₃ φ)) ≤ r := by
    intro φ σ hσ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    obtain ⟨φ', hφ'⟩ := D.cyclic φ
    obtain ⟨φ'', hφ''⟩ := D.cyclic φ'
    obtain ⟨k1, k2, k3⟩ := D.theta_cyclic hφ'
    obtain ⟨l1, l2, l3⟩ := D.theta_cyclic hφ''
    rcases hσ with h_id | h_c | h_c2
    · subst h_id
      have h_pt : permuteTriple (Equiv.refl _) (D.θ₁ φ, D.θ₂ φ, D.θ₃ φ) =
          (D.θ₁ φ, D.θ₂ φ, D.θ₃ φ) := rfl
      rw [h_pt]; exact htheta φ
    · subst h_c
      have h_pt : permuteTriple cyclicPerm3 (D.θ₁ φ, D.θ₂ φ, D.θ₃ φ) =
          (D.θ₃ φ, D.θ₁ φ, D.θ₂ φ) := rfl
      rw [h_pt]
      -- θ(φ'') = (θ₂ φ', θ₃ φ', θ₁ φ') = (θ₃ φ, θ₁ φ, θ₂ φ).
      have e1 : D.θ₁ φ'' = D.θ₃ φ := by rw [l1, k2]
      have e2 : D.θ₂ φ'' = D.θ₁ φ := by rw [l2, k3]
      have e3 : D.θ₃ φ'' = D.θ₂ φ := by rw [l3, k1]
      have := htheta φ''
      rw [e1, e2, e3] at this; exact this
    · subst h_c2
      have h_pt : permuteTriple (cyclicPerm3 * cyclicPerm3) (D.θ₁ φ, D.θ₂ φ, D.θ₃ φ) =
          (D.θ₂ φ, D.θ₃ φ, D.θ₁ φ) := rfl
      rw [h_pt]
      -- θ(φ') = (θ₂ φ, θ₃ φ, θ₁ φ).
      have e1 : D.θ₁ φ' = D.θ₂ φ := k1
      have e2 : D.θ₂ φ' = D.θ₃ φ := k2
      have e3 : D.θ₃ φ' = D.θ₁ φ := k3
      have := htheta φ'
      rw [e1, e2, e3] at this; exact this
  -- Step 4: Jensen averaging.
  have h_avg : ∀ φ : AsymptoticSpectrumPoint R P,
      F ((D.θ₁ φ + D.θ₂ φ + D.θ₃ φ) / 3,
         (D.θ₁ φ + D.θ₂ φ + D.θ₃ φ) / 3,
         (D.θ₁ φ + D.θ₂ φ + D.θ₃ φ) / 3) ≤ r := fun φ =>
    jensen_S3_convex hF_convex (D.θ₁ φ, D.θ₂ φ, D.θ₃ φ) r (hF_perm φ)
  -- Step 5: take the maximizing spectrum point and conclude.
  set S : AsymptoticSpectrumPoint R P → ℝ :=
    fun φ => D.θ₁ φ + D.θ₂ φ + D.θ₃ φ with hS_def
  haveI : Nonempty (AsymptoticSpectrumPoint R P) := mme_spectrum_nonempty P
  have h_compact : IsCompact (Set.univ : Set (AsymptoticSpectrumPoint R P)) := isCompact_univ
  obtain ⟨φ_max, -, hmax⟩ :=
    h_compact.exists_isMaxOn Set.univ_nonempty D.continuous_θsum.continuousOn
  have h_supS : D.omegaAbs = S φ_max := by
    apply le_antisymm
    · refine ciSup_le ?_; intro φ; exact hmax (Set.mem_univ φ)
    · exact le_ciSup (f := S)
        ⟨S φ_max, fun y ⟨φ, hφ⟩ => hφ ▸ hmax (Set.mem_univ φ)⟩ φ_max
  rw [h_supS]
  have h_at_max := h_avg φ_max
  have h_eq : ∀ i, ((n i * m i * p i : ℕ) : ℝ) ^ (S φ_max / 3) =
      (n i : ℝ) ^ (S φ_max / 3) * (m i : ℝ) ^ (S φ_max / 3) * (p i : ℝ) ^ (S φ_max / 3) := by
    intro i
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (le_of_lt (hn_pos i)) (le_of_lt (hm_pos i))]
  calc ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (S φ_max / 3)
      = ∑ i, (n i : ℝ) ^ (S φ_max / 3) * (m i : ℝ) ^ (S φ_max / 3) *
          (p i : ℝ) ^ (S φ_max / 3) :=
        Finset.sum_congr rfl fun i _ => h_eq i
    _ = F ((S φ_max) / 3, (S φ_max) / 3, (S φ_max) / 3) := rfl
    _ ≤ r := h_at_max

end MMData

end MME


