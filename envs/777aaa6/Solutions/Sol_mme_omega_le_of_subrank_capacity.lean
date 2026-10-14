-- Prove2me | solution 1 for mme_omega_le_of_subrank_capacity
-- status  : ACCEPTED   (disprove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T14:48:22.000251+00:00
-- url     : https://prove2.me/submissions/76a9821a-ad5c-4f56-8d01-625a282d7d0e

/- Credited port of ryanshin submission38d2b593-1e54-453c-b2db-a1b3a714a0e2 (433 ERROR while compiling target module, not a verified acceptance). This version is independently checked in777aaa61. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_subrank_capacity
import Definitions.Def_mme_omega_strassen
import Definitions.Def_mme_omega_pos
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_duality

open MME BigOperators Filter PiTensorProduct

variable {K : Type} [Field K]

/-! ## Quotient-algebra facts about the diagonal `I_2` -/

theorem sd_toQ_kronPow_diag (r N : ℕ) :
    TensorQ.toQ ((TensorObj.diagObj K 3 r).kronPow N) = ((r ^ N : ℕ) : TensorQ K 3) := by
  rw [TensorQ.toQ_kronPow, ← TensorQ.natCast_eq, Nat.cast_pow]

theorem sd_toQ_bigAdd_MM111 (k : ℕ) :
    TensorQ.toQ (TensorObj.bigAdd (fun _ : Fin k => MMObj K 1 1 1)) = ((k : ℕ) : TensorQ K 3) := by
  rw [TensorQ.toQ_bigAdd]
  have h1 : TensorQ.toQ (MMObj K 1 1 1) = (1 : TensorQ K 3) := MMq_one
  rw [Finset.sum_congr rfl (fun i _ => h1), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem sd_restrict_of_toQ_eq {X Y : TensorObj K 3} (h : TensorQ.toQ X = TensorQ.toQ Y) :
    TensorObj.Restrict X Y := by
  have : TensorQ.le (TensorQ.toQ X) (TensorQ.toQ Y) := by
    rw [h]; exact TensorQ.le_refl _
  exact (TensorQ.le_toQ X Y).mp this

/-- `2^N` copies of `⟨1,1,1⟩` restrict from `I_2^{⊗N}`. -/
theorem sd_restrict_bigAdd_kronPow_diag2 (N : ℕ) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin (2 ^ N) => MMObj K 1 1 1))
      ((TensorObj.diagObj K 3 2).kronPow N) :=
  sd_restrict_of_toQ_eq (by rw [sd_toQ_bigAdd_MM111, sd_toQ_kronPow_diag])

/-- `I_2^{⊗N}` restricts to `I_{2^N}`. -/
theorem sd_restrict_kronPow_diag2_diag (N : ℕ) :
    TensorObj.Restrict ((TensorObj.diagObj K 3 2).kronPow N)
      (TensorObj.diagObj K 3 (2 ^ N)) :=
  sd_restrict_of_toQ_eq (by rw [sd_toQ_kronPow_diag, TensorQ.natCast_eq])

/-! ## Asymptotic rank of `I_2` -/

theorem sd_asymptoticRank_diag2_le : tensorAsymptoticRank (TensorObj.diagObj K 3 2) ≤ 2 := by
  unfold tensorAsymptoticRank
  have hbdd : BddBelow (Set.range fun n : ℕ =>
      (tensorRankObj ((TensorObj.diagObj K 3 2).kronPow (n + 1)) : ℝ) ^ ((1 : ℝ) / (n + 1))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    positivity
  refine (ciInf_le hbdd 0).trans ?_
  have hrank : tensorRankObj ((TensorObj.diagObj K 3 2).kronPow (0 + 1)) ≤ 2 := by
    unfold tensorRankObj
    exact Nat.sInf_le (sd_restrict_kronPow_diag2_diag (K := K) 1)
  have hcast : (tensorRankObj ((TensorObj.diagObj K 3 2).kronPow (0 + 1)) : ℝ) ≤ 2 := by
    exact_mod_cast hrank
  simpa using hcast

/-- Asymptotic rank of a direct sum of MM objects restricting from `I_2^{⊗N}`. -/
theorem sd_asymptoticRank_le_of_restrict_kronPow_diag2 {k : ℕ} (a b c : Fin k → ℕ) (N : ℕ)
    (h : TensorObj.Restrict
      (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
      ((TensorObj.diagObj K 3 2).kronPow N)) :
    tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i))) ≤
      ((2 ^ N : ℕ) : ℝ) := by
  have hd : (1 : ℕ) < 3 := by norm_num
  rw [TensorQ.tensorAsymptoticRank_eq hd]
  have hle : (TensorQ.tensorStrassen K 3 hd).le
      (TensorQ.toQ (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i))))
      ((2 ^ N : ℕ) : TensorQ K 3) := by
    rw [TensorQ.natCast_eq]
    show TensorQ.le _ _
    rw [TensorQ.le_toQ]
    exact TensorObj.Restrict.trans h (sd_restrict_kronPow_diag2_diag N)
  exact StrassenPreorder.asymptoticRank_le_of_asymptoticLe_natCast _
    (AsymptoticLe.of_le _ hle)

/-! ## The exponent is at least two -/

/-- Multilinear coordinate-extraction map `m ↦ (m₁(b,a) · m₂(a,a)) • m₀`. -/
def sd_coordMap (n : ℕ) (a b : Fin n) :
    MultilinearMap K (MMSpace K n n n) (Fin n × Fin n → K) where
  toFun m := (m ⟨1, by norm_num⟩ (b, a) * m ⟨2, by norm_num⟩ (a, a)) • m ⟨0, by norm_num⟩
  map_update_add' m s x y := by
    fin_cases s
    · simp only [Function.update_self, Function.update_of_ne (show (⟨1, by norm_num⟩ : Fin 3) ≠ ⟨0, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num)),
        Function.update_of_ne (show (⟨2, by norm_num⟩ : Fin 3) ≠ ⟨0, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num))]
      rw [smul_add]
    · simp only [Function.update_self, Function.update_of_ne (show (⟨0, by norm_num⟩ : Fin 3) ≠ ⟨1, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num)),
        Function.update_of_ne (show (⟨2, by norm_num⟩ : Fin 3) ≠ ⟨1, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num))]
      rw [Pi.add_apply, add_mul, add_smul]
    · simp only [Function.update_self, Function.update_of_ne (show (⟨0, by norm_num⟩ : Fin 3) ≠ ⟨2, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num)),
        Function.update_of_ne (show (⟨1, by norm_num⟩ : Fin 3) ≠ ⟨2, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num))]
      rw [Pi.add_apply, mul_add, add_smul]
  map_update_smul' m s c x := by
    fin_cases s
    · simp only [Function.update_self, Function.update_of_ne (show (⟨1, by norm_num⟩ : Fin 3) ≠ ⟨0, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num)),
        Function.update_of_ne (show (⟨2, by norm_num⟩ : Fin 3) ≠ ⟨0, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num))]
      rw [smul_comm]
    · simp only [Function.update_self, Function.update_of_ne (show (⟨0, by norm_num⟩ : Fin 3) ≠ ⟨1, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num)),
        Function.update_of_ne (show (⟨2, by norm_num⟩ : Fin 3) ≠ ⟨1, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num))]
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_smul]
    · simp only [Function.update_self, Function.update_of_ne (show (⟨0, by norm_num⟩ : Fin 3) ≠ ⟨2, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num)),
        Function.update_of_ne (show (⟨1, by norm_num⟩ : Fin 3) ≠ ⟨2, by norm_num⟩ by exact Fin.ne_of_val_ne (by norm_num))]
      rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, mul_smul]

theorem sd_coordMap_MMTensor (n : ℕ) (a b : Fin n) :
    PiTensorProduct.lift (sd_coordMap (K := K) n a b) (MMTensor K n n n) =
      (Pi.single (a, b) (1 : K) : Fin n × Fin n → K) := by
  rw [MMTensor]
  simp only [map_sum, PiTensorProduct.lift.tprod]
  simp only [sd_coordMap, MultilinearMap.coe_mk]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single a]
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ a) h
    · intro j _ hj
      apply Finset.sum_eq_zero
      intro k _
      simp [Pi.single_apply, Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ b) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    simp [Pi.single_apply, Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem sd_single_mem_span (n r : ℕ) (f : ∀ i, (Fin r → K) →ₗ[K] MMSpace K n n n i)
    (hf : PiTensorProduct.map f (diagTensor K 3 r) = MMTensor K n n n) (a b : Fin n) :
    (Pi.single (a, b) (1 : K) : Fin n × Fin n → K) ∈
      Submodule.span K (Set.range (fun j : Fin r => f ⟨0, by norm_num⟩ (Pi.single j 1))) := by
  have hR : PiTensorProduct.lift (sd_coordMap (K := K) n a b)
      (PiTensorProduct.map f (diagTensor K 3 r)) ∈
      Submodule.span K (Set.range (fun j : Fin r => f ⟨0, by norm_num⟩ (Pi.single j 1))) := by
    rw [diagTensor]
    simp only [map_sum, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    simp only [sd_coordMap, MultilinearMap.coe_mk]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [hf, sd_coordMap_MMTensor] at hR
  exact hR

theorem sd_sq_le_of_restrict (n r : ℕ)
    (h : Restrict (MMTensor K n n n) (diagTensor K 3 r)) : n * n ≤ r := by
  obtain ⟨f, hf⟩ := h
  set u : Fin r → (Fin n × Fin n → K) := fun j => f ⟨0, by norm_num⟩ (Pi.single j 1) with hu
  have hspan : Submodule.span K (Set.range u) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin n × Fin n)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [Pi.basisFun_apply]
    exact sd_single_mem_span n r f hf a b
  have h1 : Module.finrank K (Submodule.span K (Set.range u)) ≤ Fintype.card (Fin r) :=
    finrank_range_le_card u
  rw [hspan, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin] at h1
  exact h1

theorem sd_sq_le_strassenRank (n : ℕ) (hn : 1 ≤ n) :
    n * n ≤ strassenRank (MMTensor K n n n) := by
  have hne : {r | Restrict (MMTensor K n n n) (diagTensor K 3 r)}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have := n_le_strassenRank_MMTensor (K := K) n
    unfold strassenRank at this
    rw [hemp, Nat.sInf_empty] at this
    omega
  exact le_csInf hne (fun r hr => sd_sq_le_of_restrict n r hr)


theorem sd_two_le_omega : (2 : ℝ) ≤ matMulExp_strassen K := by
  unfold matMulExp_strassen
  refine le_ciInf (fun n => ?_)
  split_ifs with hn
  · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos hn1
    rw [le_div_iff₀ hlog]
    have h := sd_sq_le_strassenRank (K := K) n (by omega)
    have hpos : (0 : ℝ) < (n : ℝ) * n := by positivity
    calc 2 * Real.log n = Real.log ((n : ℝ) * n) := by
          rw [← sq, Real.log_pow]; push_cast; ring
      _ ≤ Real.log (strassenRank (MMTensor K n n n) : ℝ) :=
          Real.log_le_log hpos (by exact_mod_cast h)
  · norm_num


/-! ## The capacity set of `I_2` -/

/-- `2` belongs to the defining set of `subrankCapacity (diagObj K 3 2)`. -/
theorem sd_two_mem_capacitySet :
    (2 : ℝ) ∈ { V : ℝ | 1 ≤ V ∧
      ∀ ε > (0 : ℝ), ∃ᶠ N in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((TensorObj.diagObj K 3 2).kronPow N)
          ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) } := by
  refine ⟨by norm_num, fun ε hε => ?_⟩
  refine Filter.Eventually.frequently (Filter.Eventually.of_forall (fun N => ?_))
  refine ⟨2 ^ N, fun _ => 1, fun _ => 1, fun _ => 1, sd_restrict_bigAdd_kronPow_diag2 N, ?_⟩
  simp only [mul_one, Nat.cast_one, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  nlinarith

/-- Every member of the defining set of `subrankCapacity (diagObj K 3 2)` is at most `2`. -/
theorem sd_capacitySet_le_two (W : ℝ)
    (hW : W ∈ { V : ℝ | 1 ≤ V ∧
      ∀ ε > (0 : ℝ), ∃ᶠ N in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((TensorObj.diagObj K 3 2).kronPow N)
          ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) }) :
    W ≤ 2 := by
  obtain ⟨_, hfreq⟩ := hW
  by_contra hlt
  rw [not_le] at hlt
  have hgt : (1 : ℝ) < W / 2 := by linarith
  have hev : ∀ᶠ N : ℕ in atTop, (3 : ℝ) ≤ (W / 2) ^ N :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_ge_atTop 3
  obtain ⟨N, ⟨k, a, b, c, hres, hineq⟩, hN⟩ :=
    ((hfreq (1 / 2) (by norm_num)).and_eventually hev).exists
  have hω : (1 : ℝ) ≤ matMulExp_strassen K := one_le_matMulExp_strassen
  have hsum : ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤
      ((2 ^ N : ℕ) : ℝ) :=
    mme_sum_inequality a b c (2 ^ N) (sd_asymptoticRank_le_of_restrict_kronPow_diag2 a b c N hres)
  have hterm : ∀ i, ((a i * b i * c i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
      ((a i * b i * c i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) := by
    intro i
    rcases Nat.eq_zero_or_pos (a i * b i * c i) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.zero_rpow (by norm_num), Real.zero_rpow (by linarith)]
    · have h1 : (1 : ℝ) ≤ ((a i * b i * c i : ℕ) : ℝ) := by exact_mod_cast hpos
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have hmain : W ^ N * (1 - 1 / 2) ≤ ((2 ^ N : ℕ) : ℝ) :=
    hineq.trans ((Finset.sum_le_sum (fun i _ => hterm i)).trans hsum)
  rw [Nat.cast_pow, Nat.cast_ofNat] at hmain
  have h3 : (W / 2) ^ N ≤ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem sd_two_le_subrankCapacity_diag2 :
    (2 : ℝ) ≤ subrankCapacity (TensorObj.diagObj K 3 2) := by
  unfold subrankCapacity
  exact le_csSup ⟨2, fun W hW => sd_capacitySet_le_two W hW⟩ sd_two_mem_capacitySet


theorem solution : ¬ (∀ {K : Type} [Field K] {T : TensorObj K 3} {R V : ℝ},
    tensorAsymptoticRank T ≤ R → 1 ≤ R → 1 < V → V ≤ subrankCapacity T →
    matMulExp_strassen K ≤ Real.log R / Real.log V) := by
  intro h
  have hsub : (2 : ℝ) ≤ subrankCapacity (TensorObj.diagObj ℚ 3 2) :=
    sd_two_le_subrankCapacity_diag2
  have h2 := @h ℚ _ (TensorObj.diagObj ℚ 3 2) 2 2 sd_asymptoticRank_diag2_le (by norm_num)
    (by norm_num) hsub
  have hlog : Real.log 2 / Real.log 2 = 1 := div_self (Real.log_pos one_lt_two).ne'
  rw [hlog] at h2
  have := sd_two_le_omega (K := ℚ)
  linarith
