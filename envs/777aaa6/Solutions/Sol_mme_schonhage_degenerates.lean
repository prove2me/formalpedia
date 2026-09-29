-- Prove2me | solution 1 for mme_schonhage_degenerates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-28T22:24:08.574242+00:00
-- url     : https://prove2.me/submissions/60fe4deb-13ed-4074-981d-e3fd5178b8e6

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank

/-! # Schönhage's explicit degeneration: `⟨4,1,4⟩ ⊕ ⟨1,9,1⟩` from `I₁₇` at order 2.

The constructive heart of the ω < 2.55 bound.  Adapted from Prism's
`schonhage_direct_sum` (≈600 LOC) to the concrete MME definitions
(`PolyFamily`/`coeff` on `TensorObj`, with `PiTensorProduct.map`).  Specialized
to `n = m = 4`, so `n-1 = m-1 = 3`, `k = 9`, `r = 4·4+1 = 17`. -/

open MME PiTensorProduct BigOperators Finset

universe u

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

namespace MME

variable {K : Type u} [Field K]

/-! ## The target object and its mode spaces -/

/-- The Schönhage target `⟨4,1,4⟩ ⊕ ⟨1,9,1⟩`, as a `TensorObj K 3`. -/
private noncomputable abbrev Xobj (K : Type u) [Field K] : TensorObj K 3 :=
  TensorObj.add (MMObj K 4 1 4) (MMObj K 1 9 1)

/-- The index equivalence `(Fin 4 × Fin 4) ⊕ Unit ≃ Fin 17`. -/
private noncomputable def idxEquiv : (Fin 4 × Fin 4) ⊕ Unit ≃ Fin 17 :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.equivPUnit (Fin 1)).symm).trans finSumFinEquiv

/-- `encode i j : Fin 9` for `i j : Fin 3`. -/
private noncomputable def encode (i j : Fin 3) : Fin 9 := finProdFinEquiv (i, j)

/-! ## Basis elements of `Xobj.V`

`Xobj.V 0 = (Fin 4 × Fin 1 → K) × (Fin 1 × Fin 9 → K)`,
`Xobj.V 1 = (Fin 1 × Fin 4 → K) × (Fin 9 × Fin 1 → K)`,
`Xobj.V 2 = (Fin 4 × Fin 4 → K) × (Fin 1 × Fin 1 → K)`. -/

private noncomputable def basisA (i : Fin 4) : (Xobj K).V ⟨0, by omega⟩ :=
  ((Pi.single (i, (0 : Fin 1)) 1 : Fin 4 × Fin 1 → K), 0)

private noncomputable def basisXc (i j : Fin 3) : (Xobj K).V ⟨0, by omega⟩ :=
  (0, (Pi.single ((0 : Fin 1), encode i j) 1 : Fin 1 × Fin 9 → K))

private noncomputable def basisB (j : Fin 4) : (Xobj K).V ⟨1, by omega⟩ :=
  ((Pi.single ((0 : Fin 1), j) 1 : Fin 1 × Fin 4 → K), 0)

private noncomputable def basisY (i j : Fin 3) : (Xobj K).V ⟨1, by omega⟩ :=
  (0, (Pi.single (encode i j, (0 : Fin 1)) 1 : Fin 9 × Fin 1 → K))

private noncomputable def basisC (j i : Fin 4) : (Xobj K).V ⟨2, by omega⟩ :=
  ((Pi.single (j, i) 1 : Fin 4 × Fin 4 → K), 0)

private noncomputable def basisZ : (Xobj K).V ⟨2, by omega⟩ :=
  (0, (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K))

/-! ## The polynomial vectors

`polyVecMain i₀ j₀` is indexed by `(i₀, j₀) : Fin 4 × Fin 4`; `polyVecCorr` is the
single correction vector indexed by `Unit`.  With `n = m = 4`, the boundary
condition `i₀.val < 3` decides whether `i₀` is one of the first 3 (interior) or
the last (which carries the negated sum). -/

private noncomputable def polyVecMain (i₀ j₀ : Fin 4) (s : Fin 3) :
    ℕ →₀ (Xobj K).V s :=
  match s with
  | ⟨0, _⟩ =>
    Finsupp.single 0 (basisA i₀) +
    (if hi : i₀.val < 3 then
      (if hj : j₀.val < 3 then
        Finsupp.single 1 (basisXc (K := K) ⟨i₀.val, hi⟩ ⟨j₀.val, hj⟩)
      else 0)
    else
      (if hj : j₀.val < 3 then
        Finsupp.single 1 (-(∑ i : Fin 3, basisXc (K := K) i ⟨j₀.val, hj⟩))
      else 0))
  | ⟨1, _⟩ =>
    Finsupp.single 0 (basisB j₀) +
    (if hi : i₀.val < 3 then
      (if hj : j₀.val < 3 then
        Finsupp.single 1 (basisY (K := K) ⟨i₀.val, hi⟩ ⟨j₀.val, hj⟩)
      else
        Finsupp.single 1 (-(∑ j : Fin 3, basisY (K := K) ⟨i₀.val, hi⟩ j)))
    else 0)
  | ⟨2, _⟩ =>
    Finsupp.single 0 (basisZ (K := K)) + Finsupp.single 2 (basisC j₀ i₀)

private noncomputable def polyVecCorr (s : Fin 3) : ℕ →₀ (Xobj K).V s :=
  match s with
  | ⟨0, _⟩ => Finsupp.single 0 (-(∑ i : Fin 4, basisA (K := K) i))
  | ⟨1, _⟩ => Finsupp.single 0 (∑ j : Fin 4, basisB (K := K) j)
  | ⟨2, _⟩ => Finsupp.single 0 (basisZ (K := K))

/-- The polynomial vectors indexed by `Fin 17`. -/
private noncomputable def vfun : Fin 17 → ∀ s : Fin 3, ℕ →₀ (Xobj K).V s :=
  fun j =>
    match idxEquiv.symm j with
    | Sum.inl (i₀, j₀) => polyVecMain i₀ j₀
    | Sum.inr () => polyVecCorr

private lemma vfun_inl (p : Fin 4 × Fin 4) :
    vfun (K := K) (idxEquiv (Sum.inl p)) = polyVecMain p.1 p.2 := by
  simp only [vfun, Equiv.symm_apply_apply]

private lemma vfun_inr (u : Unit) :
    vfun (K := K) (idxEquiv (Sum.inr u)) = polyVecCorr := by
  cases u; simp only [vfun, Equiv.symm_apply_apply]

/-! ## Building the `PolyFamily` from `vfun` -/

/-- The linear map `(Fin 17 → K) →ₗ[K] (Xobj K).V i` sending `Pi.single j 1 ↦ vfun j i k`. -/
private noncomputable def vlin (i : Fin 3) (k : ℕ) :
    (TensorObj.diagObj K 3 17).V i →ₗ[K] (Xobj K).V i :=
  (Pi.basisFun K (Fin 17)).constr K (fun j => vfun j i k)

private lemma vlin_support (i : Fin 3) :
    ∀ k : ℕ, vlin (K := K) i k ≠ 0 →
      k ∈ Finset.univ.biUnion (fun j : Fin 17 => (vfun (K := K) j i).support) := by
  intro k hne
  rw [Finset.mem_biUnion]
  by_contra hall; push Not at hall
  apply hne
  have hz : (fun j : Fin 17 => (vfun (K := K) j i) k) = (0 : Fin 17 → (Xobj K).V i) :=
    funext fun j => Finsupp.notMem_support_iff.mp (hall j (Finset.mem_univ j))
  show (Pi.basisFun K (Fin 17)).constr K (fun j => (vfun j i) k) = 0
  rw [hz]; exact map_zero _

/-- The `PolyFamily (Xobj K) (diagObj K 3 17)` realizing `vfun`. -/
private noncomputable def Phi : PolyFamily (Xobj K) (TensorObj.diagObj K 3 17) where
  A := fun i => Finsupp.onFinset _ _ (vlin_support i)

private lemma Phi_A_apply (i : Fin 3) (k : ℕ) :
    (Phi (K := K)).A i k = vlin i k := rfl

/-- `vlin i k` applied to the `j`-th standard basis vector `Pi.single j 1` is `vfun j i k`. -/
private lemma vlin_single (i : Fin 3) (k : ℕ) (j : Fin 17) :
    vlin (K := K) i k (Pi.single j 1) = (vfun j i) k := by
  show (Pi.basisFun K (Fin 17)).constr K (fun j' => (vfun j' i) k) (Pi.single j 1) = _
  rw [show (Pi.single j (1 : K) : Fin 17 → K) = (Pi.basisFun K (Fin 17)) j from
    (Pi.basisFun_apply K (Fin 17) j).symm]
  exact Module.Basis.constr_basis (Pi.basisFun K (Fin 17)) K _ j

/-! ## The `coeff` expansion -/

/-- The degree-`k` coefficient of `Phi`, expanded as a sum over `Fin 17` and
antidiagonal tuples of pure tensors built from `vfun`. -/
private lemma Phi_coeff_expand (k : ℕ) :
    (Phi (K := K)).coeff k = ∑ j : Fin 17,
      (Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun i => (vfun j i) (m i))) := by
  unfold PolyFamily.coeff
  have hY : (TensorObj.diagObj K 3 17).t =
      ∑ j : Fin 17, tprod K (fun (_ : Fin 3) => (Pi.single j 1 : Fin 17 → K)) := rfl
  simp_rw [hY]
  rw [Finset.sum_congr rfl (fun m _ =>
    map_sum (PiTensorProduct.map (fun i => (Phi (K := K)).A i (m i)))
      (fun j : Fin 17 => tprod K fun _ => (Pi.single j 1 : Fin 17 → K)) Finset.univ),
    Finset.sum_comm]
  congr 1; ext j; congr 1; ext m
  have hmap := PiTensorProduct.map_tprod (R := K) (f := fun i => (Phi (K := K)).A i (m i))
    (x := fun _ : Fin 3 => (Pi.single j 1 : Fin 17 → K))
  refine hmap.trans ?_
  congr 1; funext i
  rw [Phi_A_apply]
  exact vlin_single i (m i) j

/-- Reindex `Phi.coeff k` over `idxEquiv` into a main part (over `Fin 4 × Fin 4`)
plus the single correction part. -/
private lemma Phi_coeff_split (k : ℕ) :
    (Phi (K := K)).coeff k =
      (∑ p : Fin 4 × Fin 4, (Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun i => (polyVecMain p.1 p.2 i) (m i)))) +
      (Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun i => (polyVecCorr i) (m i))) := by
  rw [Phi_coeff_expand]
  rw [← Equiv.sum_comp (idxEquiv) (fun j => (Finset.Nat.antidiagonalTuple 3 k).sum
    (fun m => tprod K (fun i => (vfun j i) (m i))))]
  rw [Fintype.sum_sum_type]
  rw [show (∑ u : Unit, (Finset.Nat.antidiagonalTuple 3 k).sum
      (fun m => tprod K (fun i => (vfun (K := K) (idxEquiv (Sum.inr u)) i) (m i)))) =
      (Finset.Nat.antidiagonalTuple 3 k).sum
      (fun m => tprod K (fun i => (vfun (K := K) (idxEquiv (Sum.inr ())) i) (m i)))
    from by rw [Finset.univ_unique]; simp]
  rw [vfun_inr]
  congr 1

/-! ## Evaluation lemmas for the polynomial vectors -/

private lemma add_zero_aux (s : Fin 3) (x : (Xobj K).V s) : x + 0 = x := AddMonoid.add_zero x

/-- Degree-0 evaluations of `polyVecMain`. -/
private lemma polyVecMain_mode0_eval0 (i₀ j₀ : Fin 4) :
    (polyVecMain (K := K) i₀ j₀ ⟨0, by omega⟩) 0 = basisA i₀ := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_same]
  split <;> split
  all_goals first
    | (rw [Finsupp.single_apply, if_neg (by omega)]; exact add_zero_aux _ _)
    | (rw [Finsupp.zero_apply]; exact add_zero_aux _ _)

private lemma polyVecMain_mode1_eval0 (i₀ j₀ : Fin 4) :
    (polyVecMain (K := K) i₀ j₀ ⟨1, by omega⟩) 0 = basisB j₀ := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_same]
  split
  · split <;> (rw [Finsupp.single_apply, if_neg (by omega)]; exact add_zero_aux _ _)
  · rw [Finsupp.zero_apply]; exact add_zero_aux _ _

private lemma polyVecMain_mode2_eval0 (i₀ j₀ : Fin 4) :
    (polyVecMain (K := K) i₀ j₀ ⟨2, by omega⟩) 0 = basisZ := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, if_neg (by omega)]
  exact add_zero_aux _ _

/-- `polyVecCorr` only has degree-0 terms. -/
private lemma polyVecCorr_eval_pos (s : Fin 3) {k : ℕ} (hk : 0 < k) :
    (polyVecCorr (K := K) s) k = 0 := by
  fin_cases s <;> simp only [polyVecCorr] <;>
    rw [Finsupp.single_apply, if_neg (by omega)]

private lemma polyVecMain_mode2_eval1 (i₀ j₀ : Fin 4) :
    (polyVecMain (K := K) i₀ j₀ ⟨2, by omega⟩) 1 = 0 := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
      Finsupp.single_eq_of_ne' (show (2:ℕ) ≠ 1 from by omega)]
  exact AddMonoid.add_zero _

/-- Mode-0 degree-1 sum cancellation. -/
private lemma sum_mode0_eval1 (j₀ : Fin 4) :
    (∑ i₀ : Fin 4, (polyVecMain (K := K) i₀ j₀ (0 : Fin 3)) (1 : ℕ)) = 0 := by
  have h_ev : ∀ i₀ : Fin 4, (polyVecMain (K := K) i₀ j₀ (0 : Fin 3)) (1 : ℕ) =
      if hi : i₀.val < 3 then
        if hj : j₀.val < 3 then basisXc ⟨i₀.val, hi⟩ ⟨j₀.val, hj⟩ else 0
      else
        if hj : j₀.val < 3 then -(∑ i, basisXc i ⟨j₀.val, hj⟩) else 0 := by
    intro i₀; simp only [polyVecMain]
    change (Finsupp.single (0:ℕ) (basisA i₀) + _) (1:ℕ) = _
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
        AddMonoid.zero_add]
    split <;> split <;> first | exact Finsupp.single_eq_same | exact Finsupp.zero_apply
  simp_rw [h_ev]
  by_cases hj : j₀.val < 3
  · simp_rw [dif_pos hj]
    have hn1 : (3 : ℕ) + 1 = 4 := by omega
    rw [← Equiv.sum_comp (finCongr hn1), Fin.sum_univ_castSucc]
    have h_lt : ∀ i : Fin 3,
        (if hi : (finCongr hn1 (Fin.castSucc i)).val < 3
          then basisXc (K := K) ⟨(finCongr hn1 (Fin.castSucc i)).val, hi⟩ ⟨j₀.val, hj⟩
          else -(∑ i, basisXc i ⟨j₀.val, hj⟩)) =
        basisXc i ⟨j₀.val, hj⟩ := by
      intro i
      have hic : (finCongr hn1 (Fin.castSucc i)).val < 3 := by simp [finCongr, Fin.castSucc]
      rw [dif_pos hic]; congr 1
    have h_last :
        (if hi : (finCongr hn1 (Fin.last 3)).val < 3
          then basisXc (K := K) ⟨(finCongr hn1 (Fin.last 3)).val, hi⟩ ⟨j₀.val, hj⟩
          else -(∑ i, basisXc i ⟨j₀.val, hj⟩)) =
        -(∑ i, basisXc i ⟨j₀.val, hj⟩) := by
      rw [dif_neg (by simp [finCongr, Fin.last])]
    simp_rw [h_lt]; rw [h_last]; exact add_neg_cancel _
  · simp_rw [dif_neg hj]; simp only [dite_eq_ite, ite_self, Finset.sum_const]; exact nsmul_zero _

/-- Mode-1 degree-1 sum cancellation. -/
private lemma sum_mode1_eval1 (i₀ : Fin 4) :
    (∑ j₀ : Fin 4, (polyVecMain (K := K) i₀ j₀ (1 : Fin 3)) (1 : ℕ)) = 0 := by
  have h_ev : ∀ j₀ : Fin 4, (polyVecMain (K := K) i₀ j₀ (1 : Fin 3)) (1 : ℕ) =
      if hi : i₀.val < 3 then
        if hj : j₀.val < 3 then basisY ⟨i₀.val, hi⟩ ⟨j₀.val, hj⟩
        else -(∑ j, basisY ⟨i₀.val, hi⟩ j)
      else 0 := by
    intro j₀; simp only [polyVecMain]
    change (Finsupp.single (0:ℕ) (basisB j₀) + _) (1:ℕ) = _
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
        AddMonoid.zero_add]
    split
    · split <;> exact Finsupp.single_eq_same
    · exact Finsupp.zero_apply
  simp_rw [h_ev]
  by_cases hi : i₀.val < 3
  · simp_rw [dif_pos hi]
    have hm1 : (3 : ℕ) + 1 = 4 := by omega
    rw [← Equiv.sum_comp (finCongr hm1), Fin.sum_univ_castSucc]
    have h_lt : ∀ j : Fin 3,
        (if hj : (finCongr hm1 (Fin.castSucc j)).val < 3
          then basisY (K := K) ⟨i₀.val, hi⟩ ⟨(finCongr hm1 (Fin.castSucc j)).val, hj⟩
          else -(∑ j, basisY ⟨i₀.val, hi⟩ j)) =
        basisY ⟨i₀.val, hi⟩ j := by
      intro j
      have hjc : (finCongr hm1 (Fin.castSucc j)).val < 3 := by simp [finCongr, Fin.castSucc]
      rw [dif_pos hjc]; congr 1
    have h_last :
        (if hj : (finCongr hm1 (Fin.last 3)).val < 3
          then basisY (K := K) ⟨i₀.val, hi⟩ ⟨(finCongr hm1 (Fin.last 3)).val, hj⟩
          else -(∑ j, basisY ⟨i₀.val, hi⟩ j)) =
        -(∑ j, basisY ⟨i₀.val, hi⟩ j) := by
      rw [dif_neg (by simp [finCongr, Fin.last])]
    simp_rw [h_lt]; rw [h_last]; exact add_neg_cancel _
  · simp_rw [dif_neg hi]; exact Finset.sum_eq_zero (fun _ _ => rfl)

private lemma polyVecMain_mode0_eval_ge2 (i₀ j₀ : Fin 4) {k : ℕ} (hk : 2 ≤ k) :
    (polyVecMain (K := K) i₀ j₀ ⟨0, by omega⟩) k = 0 := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega : (0 : ℕ) ≠ k)]
  split <;> split
  all_goals first
    | (rw [Finsupp.single_eq_of_ne' (by omega : (1 : ℕ) ≠ k)]; exact AddMonoid.zero_add _)
    | (rw [Finsupp.zero_apply]; exact AddMonoid.zero_add _)

private lemma polyVecMain_mode1_eval_ge2 (i₀ j₀ : Fin 4) {k : ℕ} (hk : 2 ≤ k) :
    (polyVecMain (K := K) i₀ j₀ ⟨1, by omega⟩) k = 0 := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega : (0 : ℕ) ≠ k)]
  split
  · split
    all_goals (rw [Finsupp.single_eq_of_ne' (by omega : (1 : ℕ) ≠ k)]; exact AddMonoid.zero_add _)
  · rw [Finsupp.zero_apply]; exact AddMonoid.zero_add _

private lemma polyVecMain_mode2_eval2 (i₀ j₀ : Fin 4) :
    (polyVecMain (K := K) i₀ j₀ ⟨2, by omega⟩) 2 = basisC j₀ i₀ := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega : (0 : ℕ) ≠ 2),
      Finsupp.single_eq_same]
  exact AddMonoid.zero_add _

/-! ## The degree-0 coefficient vanishes -/

private lemma coeff_zero : (Phi (K := K)).coeff 0 = 0 := by
  rw [Phi_coeff_split]
  simp only [Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton, Pi.zero_apply]
  -- the common degree-0 pure tensor v₀
  set v₀ : ∀ i : Fin 3, (Xobj K).V i := fun i =>
    match i with
    | ⟨0, _⟩ => ∑ i₀ : Fin 4, basisA i₀
    | ⟨1, _⟩ => ∑ j₀ : Fin 4, basisB j₀
    | ⟨2, _⟩ => basisZ with hv₀
  have h_main : (∑ x : Fin 4 × Fin 4,
      tprod K (fun i => (polyVecMain (K := K) x.1 x.2 i) 0)) = tprod K v₀ := by
    have h_eval : ∀ (i₀ j₀ : Fin 4),
        (fun i => (polyVecMain (K := K) i₀ j₀ i) 0) =
        Function.update (Function.update v₀ ⟨0, by omega⟩ (basisA i₀))
          ⟨1, by omega⟩ (basisB j₀) := by
      intro i₀ j₀; funext i; fin_cases i
      · rw [polyVecMain_mode0_eval0, Function.update_of_ne (by decide), Function.update_self]
      · rw [polyVecMain_mode1_eval0, Function.update_self]
      · rw [polyVecMain_mode2_eval0, Function.update_of_ne (by decide),
            Function.update_of_ne (by decide)]
    simp_rw [Fintype.sum_prod_type, h_eval]
    simp_rw [← (PiTensorProduct.tprod K).map_update_sum (t := Finset.univ)
      (i := (⟨1, by omega⟩ : Fin 3))]
    simp_rw [show (∑ j₀ : Fin 4, basisB (K := K) j₀) = v₀ ⟨1, by omega⟩ from by simp [hv₀]]
    simp_rw [Function.update_comm (show (⟨0, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ from by decide)]
    simp_rw [Function.update_eq_self]
    rw [← (PiTensorProduct.tprod K).map_update_sum (t := Finset.univ)
      (i := (⟨0, by omega⟩ : Fin 3))]
    simp_rw [show (∑ i₀ : Fin 4, basisA (K := K) i₀) = v₀ ⟨0, by omega⟩ from by simp [hv₀]]
    rw [Function.update_eq_self]
  have h_corr : (tprod K (fun i => (polyVecCorr (K := K) i) 0)) = -(tprod K v₀) := by
    have hc0 : (polyVecCorr (K := K) ⟨0, by omega⟩) 0 = -(∑ i : Fin 4, basisA i) := by
      simp only [polyVecCorr]; exact Finsupp.single_eq_same
    have hc1 : (polyVecCorr (K := K) ⟨1, by omega⟩) 0 = ∑ j : Fin 4, basisB j := by
      simp only [polyVecCorr]; exact Finsupp.single_eq_same
    have hc2 : (polyVecCorr (K := K) ⟨2, by omega⟩) 0 = basisZ := by
      simp only [polyVecCorr]; exact Finsupp.single_eq_same
    have h_eq : (fun i => (polyVecCorr (K := K) i) 0) =
        Function.update v₀ ⟨0, by omega⟩ (-(v₀ ⟨0, by omega⟩)) := by
      funext i; fin_cases i
      · rw [hc0, Function.update_self]
      · rw [hc1, Function.update_of_ne (by decide)]
      · rw [hc2, Function.update_of_ne (by decide)]
    rw [h_eq, (PiTensorProduct.tprod K).map_update_neg, Function.update_eq_self]
  rw [h_main, h_corr, add_neg_cancel]

/-! ## The degree-1 coefficient vanishes -/

private lemma coeff_one : (Phi (K := K)).coeff 1 = 0 := by
  rw [Phi_coeff_split]
  -- Correction part vanishes: polyVecCorr only has degree-0 terms.
  have h_corr : (Finset.Nat.antidiagonalTuple 3 1).sum
      (fun m => tprod K (fun i => (polyVecCorr (K := K) i) (m i))) = 0 := by
    apply Finset.sum_eq_zero; intro m1 hm1
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hm1
    have ⟨i, hi⟩ : ∃ i : Fin 3, 0 < m1 i := by
      by_contra h; push Not at h
      have := (h 0).antisymm (Nat.zero_le _); have := (h 1).antisymm (Nat.zero_le _)
      have := (h 2).antisymm (Nat.zero_le _); omega
    exact (PiTensorProduct.tprod K).map_coord_zero i (polyVecCorr_eval_pos i hi)
  rw [h_corr, add_zero]
  -- Main part: swap sums, each antidiag tuple contributes 0.
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero; intro m1 hm1
  rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hm1
  -- Case analysis: m1 0 + m1 1 + m1 2 = 1
  rcases Nat.eq_zero_or_pos (m1 2) with h2z | h2p
  · rcases Nat.eq_zero_or_pos (m1 1) with h1z | h1p
    · -- m1 = (1, 0, 0): cancellation in mode 0
      have h_func : ∀ (i₀ j₀ : Fin 4),
          (fun s => (polyVecMain (K := K) i₀ j₀ s) (m1 s)) =
          Function.update
            (Function.update (Function.update (0 : ∀ s : Fin 3, (Xobj K).V s)
              ⟨1, by omega⟩ (basisB j₀)) ⟨2, by omega⟩ basisZ)
            ⟨0, by omega⟩ ((polyVecMain (K := K) i₀ j₀ ⟨0, by omega⟩) 1) := by
        have h1z' : m1 ⟨1, by omega⟩ = 0 := h1z
        have h2z' : m1 ⟨2, by omega⟩ = 0 := h2z
        intro i₀ j₀; funext s; fin_cases s <;> simp only []
        · simp only [Function.update_self]; congr 1
          show m1 ⟨0, by omega⟩ = 1
          have e0 : m1 ⟨0, by omega⟩ = m1 0 := rfl
          rw [e0]; omega
        · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
              Function.update_self, h1z']
          exact polyVecMain_mode1_eval0 i₀ j₀
        · rw [Function.update_of_ne (by simp), Function.update_self, h2z']
          exact polyVecMain_mode2_eval0 i₀ j₀
      simp_rw [h_func, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp_rw [← (PiTensorProduct.tprod K).map_update_sum (t := Finset.univ)
        (i := (⟨0, by omega⟩ : Fin 3))]
      exact Finset.sum_eq_zero fun j₀ _ =>
        (PiTensorProduct.tprod K).map_coord_zero ⟨0, by omega⟩ (by
          rw [Function.update_self]; exact sum_mode0_eval1 j₀)
    · -- m1 = (0, 1, 0): cancellation in mode 1
      have h0z : m1 0 = 0 := by omega
      have h_func : ∀ (i₀ j₀ : Fin 4),
          (fun s => (polyVecMain (K := K) i₀ j₀ s) (m1 s)) =
          Function.update
            (Function.update (Function.update (0 : ∀ s : Fin 3, (Xobj K).V s)
              ⟨0, by omega⟩ (basisA i₀)) ⟨2, by omega⟩ basisZ)
            ⟨1, by omega⟩ ((polyVecMain (K := K) i₀ j₀ ⟨1, by omega⟩) 1) := by
        have h0z' : m1 ⟨0, by omega⟩ = 0 := h0z
        have h2z' : m1 ⟨2, by omega⟩ = 0 := h2z
        intro i₀ j₀; funext s; fin_cases s <;> simp only []
        · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
              Function.update_self, h0z']
          exact polyVecMain_mode0_eval0 i₀ j₀
        · simp only [Function.update_self]; congr 1
          show m1 ⟨1, by omega⟩ = 1
          have e1 : m1 ⟨1, by omega⟩ = m1 1 := rfl
          rw [e1]; omega
        · rw [Function.update_of_ne (by simp), Function.update_self, h2z']
          exact polyVecMain_mode2_eval0 i₀ j₀
      simp_rw [h_func, Fintype.sum_prod_type]
      simp_rw [← (PiTensorProduct.tprod K).map_update_sum (t := Finset.univ)
        (i := (⟨1, by omega⟩ : Fin 3))]
      exact Finset.sum_eq_zero fun i₀ _ =>
        (PiTensorProduct.tprod K).map_coord_zero ⟨1, by omega⟩ (by
          rw [Function.update_self]; exact sum_mode1_eval1 i₀)
  · -- m1 = (0, 0, 1): mode 2 at degree 1 = 0 for all polyVecMain
    have h2e : m1 2 = 1 := by omega
    apply Finset.sum_eq_zero; intro x _
    apply (PiTensorProduct.tprod K).map_coord_zero ⟨2, by omega⟩
    show (polyVecMain (K := K) x.1 x.2 ⟨2, by omega⟩) (m1 ⟨2, by omega⟩) = 0
    rw [show (m1 : Fin 3 → ℕ) ⟨2, by omega⟩ = 1 from h2e]
    exact polyVecMain_mode2_eval1 x.1 x.2

/-! ## The degree-2 coefficient equals the target tensor -/

/-- Explicit form of `(MMObj K n m p).t`. -/
private lemma MMObj_t_explicit (n m p : ℕ) : (MMObj K n m p).t =
    ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, tprod K (fun s : Fin 3 =>
      match s with
      | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
      | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
      | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K)) := rfl

/-- The target tensor `(Xobj K).t`. -/
private lemma Xobj_t_eq :
    (Xobj K).t =
      PiTensorProduct.map (fun i => LinearMap.inl K ((MMObj K 4 1 4).V i) ((MMObj K 1 9 1).V i))
        (MMObj K 4 1 4).t +
      PiTensorProduct.map (fun i => LinearMap.inr K ((MMObj K 4 1 4).V i) ((MMObj K 1 9 1).V i))
        (MMObj K 1 9 1).t := rfl

private lemma coeff_two : (Phi (K := K)).coeff 2 = (Xobj K).t := by
  rw [Phi_coeff_split]
  -- correction vanishes at degree 2
  have h_corr : (Finset.Nat.antidiagonalTuple 3 2).sum
      (fun m => tprod K (fun i => (polyVecCorr (K := K) i) (m i))) = 0 := by
    apply Finset.sum_eq_zero; intro m1 hm1
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hm1
    have ⟨i, hi⟩ : ∃ i : Fin 3, 0 < m1 i := by
      by_contra h; push Not at h
      have := (h 0).antisymm (Nat.zero_le _); have := (h 1).antisymm (Nat.zero_le _)
      have := (h 2).antisymm (Nat.zero_le _); omega
    exact (PiTensorProduct.tprod K).map_coord_zero i (polyVecCorr_eval_pos i hi)
  rw [h_corr, add_zero]
  -- expand RHS, swap main sum
  rw [Xobj_t_eq, Finset.sum_comm]
  -- the two contributing degree tuples
  set d002 : Fin 3 → ℕ := fun i => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 0 | ⟨2,_⟩ => 2
    with hd002_def
  set d110 : Fin 3 → ℕ := fun i => match i with | ⟨0,_⟩ => 1 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 0
    with hd110_def
  have hd002 : d002 ∈ Finset.Nat.antidiagonalTuple 3 2 := by
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]; rfl
  have hd110 : d110 ∈ Finset.Nat.antidiagonalTuple 3 2 := by
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]; rfl
  have hne : d110 ≠ d002 := by
    intro h; exact absurd (congr_fun h ⟨0, by omega⟩) (by simp [d002, d110])
  rw [← Finset.add_sum_erase _ _ hd002]
  have hd110e : d110 ∈ (Finset.Nat.antidiagonalTuple 3 2).erase d002 :=
    Finset.mem_erase.mpr ⟨hne, hd110⟩
  rw [← Finset.add_sum_erase _ _ hd110e]
  -- residual = 0
  have h_resid : (∑ x ∈ ((Finset.Nat.antidiagonalTuple 3 2).erase d002).erase d110,
      ∑ x_1 : Fin 4 × Fin 4,
        tprod K (fun i => (polyVecMain (K := K) x_1.1 x_1.2 i) (x i))) = 0 := by
    apply Finset.sum_eq_zero; intro m1 hm1
    simp only [Finset.mem_erase] at hm1
    obtain ⟨hne1, hne2, hmem⟩ := hm1
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hmem
    apply Finset.sum_eq_zero; intro x _
    have key : m1 (0 : Fin 3) ≥ 2 ∨ m1 (1 : Fin 3) ≥ 2 ∨ m1 (2 : Fin 3) = 1 := by
      by_contra hc; push Not at hc; obtain ⟨hc0, hc1, hc2⟩ := hc
      have : m1 (2 : Fin 3) = 0 ∨ m1 (2 : Fin 3) = 2 := by omega
      rcases this with h | h
      · exact hne1 (funext fun i => by fin_cases i <;> simp_all [d110] <;> omega)
      · exact hne2 (funext fun i => by fin_cases i <;> simp_all [d002])
    rcases key with h0 | h1 | h2
    · exact (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
        (polyVecMain_mode0_eval_ge2 x.1 x.2 h0)
    · exact (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
        (polyVecMain_mode1_eval_ge2 x.1 x.2 h1)
    · exact (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
        (by rw [h2]; exact polyVecMain_mode2_eval1 x.1 x.2)
  rw [h_resid, add_zero]
  -- match each contribution to the RHS
  congr 1
  · -- d002 contribution = map inl (MMObj 4 1 4).t
    rw [MMObj_t_explicit]
    simp only [Fin.sum_univ_one, map_sum]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i₀ _ => Finset.sum_congr rfl (fun j₀ _ => ?_))
    rw [PiTensorProduct.map_tprod]
    -- LHS term: tprod (fun i => polyVecMain i₀ j₀ i (d002 i))
    show tprod K (fun s => (polyVecMain (K := K) i₀ j₀ s) (d002 s)) = _
    congr 1; funext s; fin_cases s
    · show (polyVecMain (K := K) i₀ j₀ ⟨0, by omega⟩) (d002 ⟨0, by omega⟩) = _
      rw [show d002 ⟨0, by omega⟩ = 0 from rfl, polyVecMain_mode0_eval0]; rfl
    · show (polyVecMain (K := K) i₀ j₀ ⟨1, by omega⟩) (d002 ⟨1, by omega⟩) = _
      rw [show d002 ⟨1, by omega⟩ = 0 from rfl, polyVecMain_mode1_eval0]; rfl
    · show (polyVecMain (K := K) i₀ j₀ ⟨2, by omega⟩) (d002 ⟨2, by omega⟩) = _
      rw [show d002 ⟨2, by omega⟩ = 2 from rfl, polyVecMain_mode2_eval2]; rfl
  · -- d110 contribution = map inr (MMObj 1 9 1).t
    -- terms with i₀ = 3 (last) or j₀ = 3 (last) vanish
    have h_zero_term : ∀ (i₀ j₀ : Fin 4), ¬i₀.val < 3 ∨ ¬j₀.val < 3 →
        (tprod K (fun s => (polyVecMain (K := K) i₀ j₀ s) (d110 s))) = 0 := by
      intro i₀ j₀ h; rcases h with hi | hj
      · exact (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3) (by
          show (polyVecMain (K := K) i₀ j₀ 1) (d110 1) = 0
          rw [show d110 (1 : Fin 3) = 1 from rfl]; simp only [polyVecMain]
          change (Finsupp.single (0:ℕ) (basisB j₀) + _) (1:ℕ) = _
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
              AddMonoid.zero_add, dif_neg hi]; rfl)
      · by_cases hi : i₀.val < 3
        · exact (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3) (by
            show (polyVecMain (K := K) i₀ j₀ 0) (d110 0) = 0
            rw [show d110 (0 : Fin 3) = 1 from rfl]; simp only [polyVecMain]
            change (Finsupp.single (0:ℕ) (basisA i₀) + _) (1:ℕ) = _
            rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
                AddMonoid.zero_add, dif_pos hi, dif_neg hj]; rfl)
        · exact (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3) (by
            show (polyVecMain (K := K) i₀ j₀ 1) (d110 1) = 0
            rw [show d110 (1 : Fin 3) = 1 from rfl]; simp only [polyVecMain]
            change (Finsupp.single (0:ℕ) (basisB j₀) + _) (1:ℕ) = _
            rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
                AddMonoid.zero_add, dif_neg hi]; rfl)
    rw [Fintype.sum_prod_type]
    have hn1 : (3 : ℕ) + 1 = 4 := by omega
    have hm1 : (3 : ℕ) + 1 = 4 := by omega
    -- Step A: reindex/split the outer i₀-sum (Fin 4 -> Fin 3 + last)
    rw [← Equiv.sum_comp (finCongr hn1), Fin.sum_univ_castSucc]
    rw [show (∑ j₀, (tprod K (fun s => (polyVecMain (K := K) (finCongr hn1 (Fin.last 3)) j₀ s)
        (d110 s)))) = 0
      from Finset.sum_eq_zero fun j₀ _ =>
        h_zero_term _ j₀ (Or.inl (by simp [finCongr, Fin.last]))]
    rw [add_zero]
    -- Step B: for each interior i, reindex/split the inner j₀-sum
    rw [show (∑ i : Fin 3, ∑ j₀ : Fin 4,
          (tprod K (fun s => (polyVecMain (K := K) (finCongr hn1 (Fin.castSucc i)) j₀ s)
            (d110 s)))) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          (tprod K (fun s => (polyVecMain (K := K) (finCongr hn1 (Fin.castSucc i))
            (finCongr hm1 (Fin.castSucc j)) s) (d110 s)))
      from Finset.sum_congr rfl fun i _ => by
        rw [← Equiv.sum_comp (finCongr hm1), Fin.sum_univ_castSucc,
          show (tprod K (fun s => (polyVecMain (K := K) (finCongr hn1 (Fin.castSucc i))
            (finCongr hm1 (Fin.last 3)) s) (d110 s))) = 0
          from h_zero_term _ _ (Or.inr (by simp [finCongr, Fin.last])), add_zero]]
    -- Step C: collapse RHS Fin-1 sums; reindex RHS Fin 9 sum to Fin 3 × Fin 3 = encode
    conv_rhs => rw [MMObj_t_explicit]; simp only [Fin.sum_univ_one, map_sum]
    conv_rhs =>
      rw [← Equiv.sum_comp (finProdFinEquiv (m := 3) (n := 3))
        (fun x : Fin 9 =>
          (PiTensorProduct.map
            (fun i => LinearMap.inr K ((MMObj K 4 1 4).V i) ((MMObj K 1 9 1).V i)))
            (tprod K (fun s : Fin 3 =>
              match s with
              | ⟨0, _⟩ => (Pi.single ((0 : Fin 1), x) 1 : Fin 1 × Fin 9 → K)
              | ⟨1, _⟩ => (Pi.single (x, (0 : Fin 1)) 1 : Fin 9 × Fin 1 → K)
              | ⟨2, _⟩ => (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)))),
        Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [PiTensorProduct.map_tprod]
    show tprod K (fun s => (polyVecMain (K := K) (finCongr hn1 (Fin.castSucc i))
      (finCongr hm1 (Fin.castSucc j)) s) (d110 s)) = _
    congr 1; funext s; fin_cases s
    · -- mode 0 at degree 1 = basisXc = inr (Pi.single (0, encode i j) 1)
      show (polyVecMain (K := K) _ _ ⟨0, by omega⟩) (d110 ⟨0, by omega⟩) = _
      rw [show d110 ⟨0, by omega⟩ = 1 from rfl]; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega), AddMonoid.zero_add,
          dif_pos (show (finCongr hn1 (Fin.castSucc i)).val < 3 by simp [finCongr, Fin.castSucc]),
          dif_pos (show (finCongr hm1 (Fin.castSucc j)).val < 3 by simp [finCongr, Fin.castSucc]),
          Finsupp.single_eq_same]
      simp only [basisXc, encode, finCongr, Fin.castSucc, Equiv.coe_fn_mk]
      exact (LinearMap.inr_apply _).symm
    · -- mode 1 at degree 1 = basisY = inr (Pi.single (encode i j, 0) 1)
      show (polyVecMain (K := K) _ _ ⟨1, by omega⟩) (d110 ⟨1, by omega⟩) = _
      rw [show d110 ⟨1, by omega⟩ = 1 from rfl]; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega), AddMonoid.zero_add,
          dif_pos (show (finCongr hn1 (Fin.castSucc i)).val < 3 by simp [finCongr, Fin.castSucc]),
          dif_pos (show (finCongr hm1 (Fin.castSucc j)).val < 3 by simp [finCongr, Fin.castSucc]),
          Finsupp.single_eq_same]
      simp only [basisY, encode, finCongr, Fin.castSucc, Equiv.coe_fn_mk]
      exact (LinearMap.inr_apply _).symm
    · -- mode 2 at degree 0 = basisZ = inr (Pi.single (0, 0) 1)
      show (polyVecMain (K := K) _ _ ⟨2, by omega⟩) (d110 ⟨2, by omega⟩) = _
      rw [show d110 ⟨2, by omega⟩ = 0 from rfl]; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne' (by omega)]
      exact add_zero_aux _ _

/-! ## The main theorem -/

theorem solution {K : Type u} [Field K] :
    DegeneratesOfOrder (TensorObj.bigAdd ![MMObj K 4 1 4, MMObj K 1 9 1])
      (TensorObj.diagObj K 3 17) 2 := by
  refine ⟨Phi, ?_, ?_⟩
  · intro k hk
    match k, hk with
    | 0, _ => exact coeff_zero
    | 1, _ => exact coeff_one
  · exact coeff_two

end MME

open MME in
/-- Top-level alias: the platform's prover looks for `solution`, not `MME.solution`. -/
theorem solution {K : Type u} [Field K] :
    DegeneratesOfOrder (TensorObj.bigAdd ![MMObj K 4 1 4, MMObj K 1 9 1])
      (TensorObj.diagObj K 3 17) 2 :=
  MME.solution
