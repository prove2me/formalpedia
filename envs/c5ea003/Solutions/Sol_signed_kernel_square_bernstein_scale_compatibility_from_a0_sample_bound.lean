-- Prove2me | solution 1 for signed_kernel_square_bernstein_scale_compatibility_from_a0_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T03:11:35.338893+00:00
-- url     : https://prove2.me/submissions/73011c9a-875c-4d88-9317-48b3d8edd064

import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a0_min_dim
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace ProveDbcc

theorem rpow_eq (a b : ℝ) : Real.rpow a b = a ^ b := rfl

/-- `1 ≤ β log n` for `β > 2`, `n ≥ 2`. -/
theorem one_le_beta_log (β n : ℝ) (hβ : 2 < β) (hn : 2 ≤ n) (hlogpos : 0 < Real.log n) :
    (1:ℝ) ≤ β * Real.log n := by
  have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have h4 : (1:ℝ) < Real.log 4 := by
    have : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_three (by norm_num)
    calc (1:ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) this
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  nlinarith [hlog2n, hlogpos, h4, hlog4]

/-- Scalar compatibility core (plain-variable form to avoid `set`-whnf storms).
With `E = |sign entry| ≤ Csign·μ₀·rr/mm`, `nn = max`, `mm = min`, `nn·mm = n₁n₂`,
`L = β log n ≥ 1`, `mr = m`, feasibility `lam·μ₀^{4/3}·nn·rr^{4/3}·L ≤ mr ≤ nn·mm`:
  `(μ₀·rr/mm)·√L·(μ₀·nn·rr/mr)^{3/2} ≤ 1/lam`. -/
theorem core_bound
    (mu0 rr nn mm mr L lam : ℝ)
    (hmu0 : 1 ≤ mu0) (hrr : 1 ≤ rr)
    (hnn : 1 ≤ nn) (hmm : 1 ≤ mm) (hmnle : mm ≤ nn)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam)
    (hfeas_lb : lam * Real.rpow mu0 ((4:ℝ)/3) * nn * Real.rpow rr ((4:ℝ)/3) * L ≤ mr)
    (hfeas_ub : mr ≤ nn * mm) :
    (mu0 * rr / mm) * Real.sqrt L *
        Real.rpow ((mu0 * nn * rr) / mr) ((3:ℝ)/2) ≤ 1 / lam := by
  have hmu0p : (0:ℝ) < mu0 := by linarith
  have hrrp : (0:ℝ) < rr := by linarith
  have hnnp : (0:ℝ) < nn := by linarith
  have hmmp : (0:ℝ) < mm := by linarith
  have hLp : (0:ℝ) < L := by linarith
  have hlamp : (0:ℝ) < lam := by linarith
  set D : ℝ := Real.rpow mu0 ((4:ℝ)/3) with hD
  set Dr : ℝ := Real.rpow rr ((4:ℝ)/3) with hDr
  have hDp : (0:ℝ) < D := by rw [hD, rpow_eq]; exact Real.rpow_pos_of_pos hmu0p _
  have hDrp : (0:ℝ) < Dr := by rw [hDr, rpow_eq]; exact Real.rpow_pos_of_pos hrrp _
  have hlbp : (0:ℝ) < lam * D * nn * Dr * L := by positivity
  have hmrp : (0:ℝ) < mr := lt_of_lt_of_le hlbp hfeas_lb
  -- D ≥ 1, Dr ≥ 1, and the cube identities D = mu0^{4/3} so (mu0)^? handled via rpow.
  have hD1 : (1:ℝ) ≤ D := by
    rw [hD, rpow_eq]
    calc (1:ℝ) = (1:ℝ) ^ ((4:ℝ)/3) := (Real.one_rpow _).symm
      _ ≤ mu0 ^ ((4:ℝ)/3) := Real.rpow_le_rpow (by norm_num) hmu0 (by norm_num)
  have hDr1 : (1:ℝ) ≤ Dr := by
    rw [hDr, rpow_eq]
    calc (1:ℝ) = (1:ℝ) ^ ((4:ℝ)/3) := (Real.one_rpow _).symm
      _ ≤ rr ^ ((4:ℝ)/3) := Real.rpow_le_rpow (by norm_num) hrr (by norm_num)
  -- Rewrite the rpow ^(3/2) as a sqrt of the cube (all bases nonneg).
  have hbase_nn : (0:ℝ) ≤ (mu0 * nn * rr) / mr := by positivity
  have hrpow32 : Real.rpow ((mu0 * nn * rr) / mr) ((3:ℝ)/2)
      = Real.sqrt (((mu0 * nn * rr) / mr) ^ 3) := by
    rw [rpow_eq, Real.sqrt_eq_rpow, ← Real.rpow_natCast _ 3, ← Real.rpow_mul hbase_nn]
    norm_num
  rw [hrpow32]
  -- Merge √L · √(cube) = √(L · cube).
  have hcube_nn : (0:ℝ) ≤ ((mu0 * nn * rr) / mr) ^ 3 := by positivity
  have hmerge : Real.sqrt L * Real.sqrt (((mu0 * nn * rr) / mr) ^ 3)
      = Real.sqrt (L * ((mu0 * nn * rr) / mr) ^ 3) := (Real.sqrt_mul (le_of_lt hLp) _).symm
  rw [mul_assoc, hmerge]
  -- The whole LHS = (μ₀rr/mm) · √(L·(μ₀nn rr/mr)^3).  Bound by squaring.
  set pref : ℝ := mu0 * rr / mm with hpref
  have hprefnn : (0:ℝ) ≤ pref := by rw [hpref]; positivity
  have hSnn : (0:ℝ) ≤ L * ((mu0 * nn * rr) / mr) ^ 3 := by positivity
  -- Goal: pref · √S ≤ 1/lam.  Both sides ≥ 0; square it.
  have hRHSnn : (0:ℝ) ≤ 1 / lam := by positivity
  rw [show (1:ℝ)/lam = Real.sqrt ((1/lam)^2) from by
        rw [Real.sqrt_sq hRHSnn]]
  -- pref = √(pref^2); merge into one sqrt.
  rw [show pref = Real.sqrt (pref^2) from (Real.sqrt_sq hprefnn).symm, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  -- Reduce to: pref^2 · L · (μ₀nn rr/mr)^3 ≤ (1/lam)^2.
  -- Use mr ≥ lb to drop mr, then the feasibility-derived bounds.
  -- Step 1: (μ₀nn rr/mr)^3 ≤ (μ₀nn rr/lb)^3   (since mr ≥ lb > 0).
  have hmr_ge_lb : lam * D * nn * Dr * L ≤ mr := hfeas_lb
  -- key algebraic facts: μ₀^2 = D·μ₀^{2/3}, etc.  We avoid fractional powers by
  -- bounding the cube directly with feasibility in polynomial form.
  -- Let num = μ₀·nn·rr.  (num/mr)^3 = num^3 / mr^3 ≤ num^3 / lb^3.
  set num : ℝ := mu0 * nn * rr with hnum
  have hnump : (0:ℝ) < num := by rw [hnum]; positivity
  have hsq_pref : pref^2 = mu0^2 * rr^2 / mm^2 := by rw [hpref]; ring
  -- target poly:  (μ₀^2 rr^2/mm^2) · L · num^3/mr^3 ≤ 1/lam^2
  -- Replace 1/(mr^3) ≤ 1/lb^3.
  have hmr3 : mr^3 ≥ (lam * D * nn * Dr * L)^3 := by
    have := hmr_ge_lb
    have h0 : (0:ℝ) ≤ lam * D * nn * Dr * L := le_of_lt hlbp
    nlinarith [pow_le_pow_left₀ h0 hmr_ge_lb 3, this]
  -- So (pref^2·L·num^3)/mr^3 ≤ (pref^2·L·num^3)/lb^3.
  have hlb3p : (0:ℝ) < (lam * D * nn * Dr * L)^3 := by positivity
  have hstep1 : pref^2 * (L * (num / mr)^3) ≤ pref^2 * (L * (num / (lam*D*nn*Dr*L))^3) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hLp)
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_left (le_of_lt hnump) hlbp hmr_ge_lb
  -- Now prove the clean bound at mr = lb:
  --   pref^2 · L · (num/lb)^3 ≤ 1/lam^2.
  -- num/lb = μ₀ nn rr / (lam D nn Dr L) = μ₀ rr / (lam D Dr L).
  have hnum_over_lb : num / (lam*D*nn*Dr*L) = mu0 * rr / (lam * D * Dr * L) := by
    rw [hnum]; field_simp
  have hclean : pref^2 * (L * (num / (lam*D*nn*Dr*L))^3) ≤ (1/lam)^2 := by
    rw [show (1/lam)^2 = 1/lam^2 from by rw [div_pow, one_pow]]
    rw [hnum_over_lb, hsq_pref]
    -- LHS = (μ₀^2 rr^2/mm^2)·L·(μ₀ rr)^3/(lam D Dr L)^3
    --     = μ₀^5 rr^5 / (mm^2 · lam^3 · D^3 · Dr^3 · L^2)
    -- Using D = μ₀^{4/3} ⇒ D^3 = μ₀^4 ; Dr^3 = rr^4.
    have hD3 : D^3 = mu0^4 := by
      rw [hD, rpow_eq, ← Real.rpow_natCast (mu0 ^ ((4:ℝ)/3)) 3, ← Real.rpow_mul (le_of_lt hmu0p),
        show ((4:ℝ)/3) * (3:ℕ) = (4:ℕ) by push_cast; ring, Real.rpow_natCast]
    have hDr3 : Dr^3 = rr^4 := by
      rw [hDr, rpow_eq, ← Real.rpow_natCast (rr ^ ((4:ℝ)/3)) 3, ← Real.rpow_mul (le_of_lt hrrp),
        show ((4:ℝ)/3) * (3:ℕ) = (4:ℕ) by push_cast; ring, Real.rpow_natCast]
    -- After substituting D^3, Dr^3 the LHS simplifies to
    --   μ₀ rr / (mm^2 · lam^3 · L^2).
    have hLHS_eq : mu0^2 * rr^2 / mm^2 * (L * (mu0 * rr / (lam * D * Dr * L))^3)
        = (mu0 * rr) / (mm^2 * lam^3 * L^2) := by
      have hpow : (lam * D * Dr * L)^3 = lam^3 * D^3 * Dr^3 * L^3 := by ring
      rw [div_pow, mul_div_assoc, hpow, hD3, hDr3]
      field_simp
    rw [hLHS_eq]
    -- Want:  μ₀ rr / (mm^2 lam^3 L^2) ≤ 1/lam^2.
    -- ⟺ μ₀ rr · lam^2 ≤ mm^2 lam^3 L^2  ⟺ μ₀ rr ≤ mm^2 lam L^2.
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- μ₀ rr · lam^2 ≤ 1 · (mm^2 lam^3 L^2)
    -- feasibility lb ≤ ub gives μ₀^{4/3} rr^{4/3} ≤ mm/(lam L) i.e. D·Dr ≤ mm/(lam L).
    have hfeasprod : lam * D * Dr * L ≤ mm := by
      -- lam D nn Dr L ≤ mr ≤ nn mm ⇒ lam D Dr L ≤ mm  (divide by nn > 0)
      have hchain : lam * D * nn * Dr * L ≤ nn * mm := le_trans hfeas_lb hfeas_ub
      have h2 : (lam * D * Dr * L) * nn ≤ mm * nn := by nlinarith [hchain]
      exact le_of_mul_le_mul_right h2 hnnp
    -- and μ₀ rr ≤ D · Dr  (since μ₀ ≤ μ₀^{4/3}=D for μ₀≥1, rr ≤ Dr).
    have hmu0_le_D : mu0 ≤ D := by
      rw [hD, rpow_eq]
      calc mu0 = mu0 ^ (1:ℝ) := (Real.rpow_one mu0).symm
        _ ≤ mu0 ^ ((4:ℝ)/3) := Real.rpow_le_rpow_of_exponent_le hmu0 (by norm_num)
    have hrr_le_Dr : rr ≤ Dr := by
      rw [hDr, rpow_eq]
      calc rr = rr ^ (1:ℝ) := (Real.rpow_one rr).symm
        _ ≤ rr ^ ((4:ℝ)/3) := Real.rpow_le_rpow_of_exponent_le hrr (by norm_num)
    -- μ₀ rr ≤ D Dr ≤ mm/(lam L) ≤ mm  ⇒  μ₀ rr ≤ mm.  But we need μ₀ rr ≤ mm^2 lam L^2.
    -- From hfeasprod: lam D Dr L ≤ mm.  Also μ₀ rr ≤ D Dr.
    -- So lam L (μ₀ rr) ≤ lam L (D Dr) = (lam D Dr L) ≤ mm.  ⇒ μ₀ rr ≤ mm/(lam L).
    have hmu0rr_le : (mu0 * rr) ≤ D * Dr := by
      have h1 : mu0 * rr ≤ D * rr := mul_le_mul_of_nonneg_right hmu0_le_D (le_of_lt hrrp)
      have h2 : D * rr ≤ D * Dr := mul_le_mul_of_nonneg_left hrr_le_Dr (le_of_lt hDp)
      linarith
    -- lam * L * (μ₀ rr) ≤ lam * L * (D Dr) = lam D Dr L ≤ mm
    have hkey : lam * L * (mu0 * rr) ≤ mm := by
      have hstep : lam * L * (mu0 * rr) ≤ lam * L * (D * Dr) :=
        mul_le_mul_of_nonneg_left hmu0rr_le (by positivity)
      have heq : lam * L * (D * Dr) = lam * D * Dr * L := by ring
      linarith [hstep, heq ▸ hfeasprod]
    -- Goal:  μ₀ rr · lam^2 ≤ 1 · (mm^2 · lam^3 · L^2).
    -- From hkey: μ₀ rr ≤ mm/(lam L), and mm ≥ 1, lam ≥ 1, L ≥ 1 ⇒ mm^2 lam L^2 ≥ mm ≥ lam L μ₀ rr.
    -- From hkey (lam L (μ₀ rr) ≤ mm) and lam,L ≥ 1:  μ₀ rr ≤ mm.
    have hlamL1 : (1:ℝ) ≤ lam * L := by nlinarith [hlam, hL]
    have hmu0rr_le_mm : mu0 * rr ≤ mm := by
      have h1 : mu0 * rr ≤ lam * L * (mu0 * rr) := by
        nlinarith [hlamL1, mul_pos hmu0p hrrp]
      linarith [h1, hkey]
    -- Goal:  μ₀ rr · lam^2 ≤ 1 · (mm^2 lam^3 L^2).
    -- μ₀ rr · lam^2 ≤ mm · lam^2  (hmu0rr_le_mm)  ≤  mm^2 lam^3 L^2  since mm ≤ mm^2, lam^2 ≤ lam^3, 1 ≤ L^2.
    have hlam2le3 : lam^2 ≤ lam^3 := by nlinarith [hlam, sq_nonneg lam]
    have hmmle : mm ≤ mm^2 := by nlinarith [hmm, hmmp]
    have hL2 : (1:ℝ) ≤ L^2 := by nlinarith [hL]
    nlinarith [mul_le_mul_of_nonneg_right hmu0rr_le_mm (by positivity : (0:ℝ) ≤ lam^2),
      hmmp, hlamp, hLp, hlam2le3, hmmle, hL2, hmm, hlam,
      mul_pos hmmp (mul_pos hlamp hlamp), mul_pos hmmp (mul_pos hmmp (mul_pos hlamp (mul_pos hlamp hlamp)))]
  exact le_trans hstep1 hclean

/-- Single sign-matrix entry is bounded by its entry sup-norm. -/
theorem entry_le_sup {n1 n2 : Nat} (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    |X i j| ≤ entrySupNorm X := by
  rw [entrySupNorm]
  refine le_trans ?_ (le_ciSup (f := fun i => ⨆ j : Fin n2, |X i j|)
    (Finite.bddAbove_range _) i)
  exact le_ciSup (f := fun j => |X i j|) (Finite.bddAbove_range _) j

end ProveDbcc

open ProveDbcc in
/-- `signed_kernel_square_bernstein_scale_compatibility_from_a0_sample_bound`.
Reduction: bound the per-entry sign value by the sign-matrix sup-norm
(`entry_sup_norm_sign_matrix_bound_from_a0_min_dim`, A0), then absorb the resulting
deterministic scalar (`√(βlog n)·(μ₀·max·r/m)^{3/2}`) into the `λ^{-1}` threshold
using the Lemma 4.6 sample lower bound (`core_bound`).  Source: Candès–Recht 2009/2012,
§6 (Bernstein / Lemma 4.6 sample-size condition). -/
theorem solution :
    ∃ Ccompat : ℝ, 0 < Ccompat ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ w : Fin n₁ × Fin n₂,
        |signMatrix S w.1 w.2| *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
              ((3 : ℝ) / 2) ≤
          Ccompat * Real.rpow lam (-1) := by
  obtain ⟨Csign, hCsign, hsignbound⟩ := entry_sup_norm_sign_matrix_bound_from_a0_min_dim
  refine ⟨Csign, hCsign, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample w
  have hn₁R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn₂
  have hμ₀0 : (0:ℝ) < μ₀ := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hr1R : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hmaxpos : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (le_max_left _ _)
  have hminpos : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hmaxR : (0:ℝ) < (↑(max n₁ n₂):ℝ) := by exact_mod_cast hmaxpos
  have hminR : (0:ℝ) < (↑(min n₁ n₂):ℝ) := by exact_mod_cast hminpos
  -- E = |sign w| ≤ Csign μ₀ (r/min)
  set E : ℝ := |signMatrix S w.1 w.2| with hEdef
  have hE0 : (0:ℝ) ≤ E := by rw [hEdef]; exact abs_nonneg _
  have hEbound : E ≤ Csign * μ₀ * ((r:ℝ) / (↑(min n₁ n₂))) := by
    rw [hEdef]
    exact le_trans (entry_le_sup (signMatrix S) w.1 w.2)
      (hsignbound n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0)
  set nn : ℝ := (↑(max n₁ n₂):ℝ) with hnn_def
  set mm : ℝ := (↑(min n₁ n₂):ℝ) with hmm_def
  set rr : ℝ := (r:ℝ) with hrr_def
  set mr : ℝ := (m:ℝ) with hmr_def
  have hnnmm : nn * mm = (n₁:ℝ) * (n₂:ℝ) := by
    rw [hnn_def, hmm_def,
      show ((↑(max n₁ n₂):ℝ)) * (↑(min n₁ n₂):ℝ) = ((max n₁ n₂ * min n₁ n₂ : ℕ):ℝ) by push_cast; ring,
      max_mul_min]; push_cast; ring
  have hlaminv : Real.rpow lam (-1) = 1 / lam := by
    rw [rpow_eq, Real.rpow_neg_one, inv_eq_one_div]
  rcases lt_or_ge nn 2 with hnnlt2 | hnn2
  · -- edge: max = 1 ⇒ log = 0 ⇒ √(βlog n) = 0 ⇒ LHS = 0.
    have hmaxnat1 : max n₁ n₂ = 1 := by
      have : (↑(max n₁ n₂):ℝ) < 2 := by rw [← hnn_def]; exact hnnlt2
      have hlt : max n₁ n₂ < 2 := by exact_mod_cast this
      omega
    have hnneq : nn = 1 := by rw [hnn_def, hmaxnat1]; norm_num
    have hlog0 : Real.log (↑(max n₁ n₂):ℝ) = 0 := by rw [← hnn_def, hnneq]; simp
    have hsqrt0 : Real.sqrt (β * Real.log (↑(max n₁ n₂):ℝ)) = 0 := by rw [hlog0]; simp
    rw [hsqrt0, hlaminv]
    simp only [mul_zero, zero_mul]
    positivity
  · -- main case: nn ≥ 2
    have hlognpos : (0:ℝ) < Real.log nn := Real.log_pos (by linarith)
    have hLL1 : (1:ℝ) ≤ β * Real.log nn := one_le_beta_log β nn hβ hnn2 hlognpos
    -- LHS ≤ (Csign μ₀ rr/mm) · √(β log nn) · (μ₀ nn rr/mr)^{3/2}
    --     = Csign · [ (μ₀ rr/mm)·√(β log nn)·(μ₀ nn rr/mr)^{3/2} ]  ≤ Csign · (1/lam)
    have hmrp : (0:ℝ) < mr := by
      have hlbpos : (0:ℝ) < lam * Real.rpow μ₀ ((4:ℝ)/3) * nn * Real.rpow rr ((4:ℝ)/3) *
          (β * Real.log nn) := by
        rw [rpow_eq, rpow_eq]
        have := Real.rpow_pos_of_pos hμ₀0 ((4:ℝ)/3)
        have := Real.rpow_pos_of_pos (show (0:ℝ) < rr by rw [hrr_def]; linarith) ((4:ℝ)/3)
        positivity
      have hsample' : lam * Real.rpow μ₀ ((4:ℝ)/3) * nn * Real.rpow rr ((4:ℝ)/3) *
          (β * Real.log nn) ≤ mr := by
        rw [hmr_def, hnn_def, hrr_def]; exact hsample
      linarith [lt_of_lt_of_le hlbpos hsample']
    -- replace β log(max) by β log nn (= same)
    have hlogeq : Real.log (↑(max n₁ n₂):ℝ) = Real.log nn := by rw [hnn_def]
    -- core_bound feasibility
    have hfeas_lb : lam * Real.rpow μ₀ ((4:ℝ)/3) * nn * Real.rpow rr ((4:ℝ)/3) *
        (β * Real.log nn) ≤ mr := by
      rw [hmr_def, hnn_def, hrr_def]; exact hsample
    have hfeas_ub : mr ≤ nn * mm := by rw [hnnmm, hmr_def]; exact_mod_cast hm
    have hrr1 : (1:ℝ) ≤ rr := by rw [hrr_def]; exact hr1R
    have hnn1 : (1:ℝ) ≤ nn := by linarith
    have hmm1 : (1:ℝ) ≤ mm := by rw [hmm_def]; exact_mod_cast hminpos
    have hmm_le_nn : mm ≤ nn := by rw [hnn_def, hmm_def]; exact_mod_cast min_le_max
    have hcore := core_bound μ₀ rr nn mm mr (β * Real.log nn) lam
      hμ₀ hrr1 hnn1 hmm1 hmm_le_nn hLL1 hlam hfeas_lb hfeas_ub
    -- Assemble.  LHS_actual = E · √(β log(max)) · (μ₀ max r/m)^{3/2}.
    -- Rewrite the rpow base/exponent args into the set-vars.
    rw [hlogeq,
      show (μ₀ * nn * rr) / mr = (μ₀ * nn * rr) / mr from rfl]
    -- E ≤ Csign μ₀ rr/mm, all other factors ≥ 0.
    have hfac_nn : (0:ℝ) ≤ Real.sqrt (β * Real.log nn) *
        Real.rpow ((μ₀ * nn * rr) / mr) ((3:ℝ)/2) := by
      rw [rpow_eq]
      have hb : (0:ℝ) ≤ (μ₀ * nn * rr) / mr := by
        have : (0:ℝ) < rr := by linarith
        positivity
      positivity
    calc E * Real.sqrt (β * Real.log nn) * Real.rpow ((μ₀ * nn * rr) / mr) ((3:ℝ)/2)
        = E * (Real.sqrt (β * Real.log nn) * Real.rpow ((μ₀ * nn * rr) / mr) ((3:ℝ)/2)) := by ring
      _ ≤ (Csign * μ₀ * ((r:ℝ) / (↑(min n₁ n₂)))) *
            (Real.sqrt (β * Real.log nn) * Real.rpow ((μ₀ * nn * rr) / mr) ((3:ℝ)/2)) :=
            mul_le_mul_of_nonneg_right hEbound hfac_nn
      _ = Csign * ((μ₀ * rr / mm) * Real.sqrt (β * Real.log nn) *
            Real.rpow ((μ₀ * nn * rr) / mr) ((3:ℝ)/2)) := by
            rw [hrr_def, hmm_def]; ring
      _ ≤ Csign * (1 / lam) := by
            apply mul_le_mul_of_nonneg_left hcore (le_of_lt hCsign)
      _ = Csign * Real.rpow lam (-1) := by rw [hlaminv]
