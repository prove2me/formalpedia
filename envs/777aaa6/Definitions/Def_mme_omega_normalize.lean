-- Prove2me | Definitions.Def_mme_omega_normalize
-- name    : mme_omega_normalize
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T15:40:08.886081+00:00
-- url     : https://prove2.me/theorems/8788a455-18e9-491c-924a-17fea41f02c0
-- statement:
--   **The Strassen-form $\omega$ equals the base-2 logarithm of the asymptotic rank of $\mathrm{MM}(2,2,2)$.**
--
--   `matMulExp_strassen_eq_log_AR`: the deepest single result of the textbook layer of the MME ω<51/20 program,
--   $$\mathrm{matMulExp\_strassen}\,K \;=\; \log_2 \bigl(\mathrm{tensorAsymptoticRank}(\mathrm{MMObj}\,K\,2\,2\,2)\bigr).$$
--   This is a port of Prism's `matMulExp_eq_log_AR_222`.
--
--   **Why this canonical normalization matters.** It is the rigorous statement that "$\omega$ is the asymptotic exponent of $2 \times 2 \times 2$ matrix multiplication" — once you have an upper bound on $\mathrm{AR}(\mathrm{MM}(2,2,2))$, you have an upper bound on $\omega$ via $\log_2$. It also pins the abstract spectral $\omega_{\mathrm{abs}} = \sup_\varphi (\theta_1 + \theta_2 + \theta_3)(\varphi)$ to the concrete `matMulExp_strassen` via Strassen duality (this is the content of `Def_mme_tensor_bridge`'s `bridge_omega`).
--
--   **Proof route.** Through the isomorphism quotient `TensorQ K 3` and its abstract preorder `tensorStrassen`:
--   1. **Rank identification** (`strassenRank_MMTensor_eq_rank`): $\mathrm{strassenRank}(\mathrm{MMTensor}\,n\,n\,n) = \mathrm{rank}_{\mathrm{tensorStrassen}}(\mathrm{toQ}(\mathrm{MMObj}\,K\,n\,n\,n))$. Combines `rank_tensorStrassen_toQ` (`Def_mme_rank_bridge`) with the defeq $\mathrm{tensorRankObj}(\mathrm{MMObj}\,n\,n\,n) = \mathrm{strassenRank}(\mathrm{MMTensor}\,n\,n\,n)$ — both are an `sInf` over the same restriction-witness set.
--   2. **Kronecker-power multiplicativity** (`Mq_pow`): $(\mathrm{toQ}\,(\mathrm{MMObj}\,K\,2\,2\,2))^k = \mathrm{toQ}\,(\mathrm{MMObj}\,K\,2^k\,2^k\,2^k)$, from `MMObj_kron_iso`.
--   3. **Fekete/squeeze** with `tends_to_asymptoticRank` (`Def_mme_spectrum`), monotonicity of `strassenRank`, and `tensorAsymptoticRank_eq` (`Def_mme_rank_bridge`) — pin the $\inf_n$ over MM-tensor sizes to the $\inf$-of-rank-powers form on `MMObj(2,2,2)`.
--
--   Sorry-free; $\#\mathrm{print\ axioms}$: only `propext`, `Classical.choice`, `Quot.sound`. Imports Mathlib + MME definitions only.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Definitions.Def_mme_omega
import Definitions.Def_mme_omega_strassen
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_omega_pos
import Definitions.Def_mme_spectrum

/-! # ω = log₂ of the asymptotic rank of the 2×2×2 matrix-multiplication tensor

The deepest single result of the textbook layer: the Strassen-form matrix-multiplication
exponent equals the base-2 logarithm of the asymptotic tensor rank of `MM(2,2,2)`,

  `matMulExp_strassen K = Real.log (tensorAsymptoticRank (MMObj K 2 2 2)) / Real.log 2`.

This is a port of Prism's `matMulExp_eq_log_AR_222`. The proof routes through the
isomorphism quotient `TensorQ K 3` and its abstract Strassen preorder `tensorStrassen`
(from `Def_mme_tensor_quotient`, re-exported via `Def_mme_rank_bridge`):

* **Rank identification** (`strassenRank_MMTensor_eq_rank`): for every `n`,
  `strassenRank (MMTensor K n n n) = StrassenPreorder.rank (tensorStrassen …) (toQ (MMObj K n n n))`.
  Combines the concrete rank reconciliation `rank_tensorStrassen_toQ` with the defeq
  `tensorRankObj (MMObj n n n) = strassenRank (MMTensor n n n)` (both `sInf` of the same
  restriction-witness set, as already exploited by `Def_mme_omega_pos`).
* **Kronecker-power multiplicativity** (`Mq_pow`): `(toQ (MMObj K 2 2 2)) ^ k =
  toQ (MMObj K (2^k) (2^k) (2^k))`, by iterating `MMObj_kron_iso` through `toQ_kronPow`.
* **Submultiplicativity + Fekete/squeeze**: the analytic core, ported verbatim from Prism
  using the abstract `rank`/`asymptoticRank`, the Fekete convergence
  `StrassenPreorder.tends_to_asymptoticRank`, and `MM`-monotonicity / sub-multiplicativity.

`tensorAsymptoticRank (MMObj K 2 2 2) = asymptoticRank (tensorStrassen …) (toQ (MMObj K 2 2 2))`
is `Def_mme_rank_bridge.tensorAsymptoticRank_eq`. -/

universe u

open PiTensorProduct TensorProduct BigOperators Filter Topology

namespace MME

variable {K : Type u} [Field K]

/-! ## Setup: the canonical preorder, the MM element, and its powers -/

/-- `1 < 3`, the fixed mode count. -/
private theorem hd3 : (1 : ℕ) < 3 := by norm_num

/-- The canonical Strassen preorder on `TensorQ K 3`. -/
private noncomputable abbrev Pcan (K : Type u) [Field K] : StrassenPreorder (TensorQ K 3) :=
  TensorQ.tensorStrassen K 3 hd3

/-! ### Restriction facts for `MMObj` (ported from `Def_mme_tensor_bridge`, which we must
not import). Each is reproved locally. -/

/-- The pure tensor `e_{ij} ⊗ e_{jk} ⊗ e_{ki}` for indices `(i,j,k)` (local copy). -/
private noncomputable def MMPure (K : Type u) [Field K] (n m p : ℕ)
    (i : Fin n) (j : Fin m) (k : Fin p) :
    PiTensorProduct K (MMSpace K n m p) :=
  tprod K (fun (s : Fin 3) =>
    match s with
    | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
    | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
    | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K))

private theorem MMObj_t_eq (n m p : ℕ) :
    (MMObj K n m p).t = ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, MMPure K n m p i j k := rfl

/-- `MMObj n m p` restricts to `MMObj n' m' p'` when `n ≤ n'`, `m ≤ m'`, `p ≤ p'`.
Port of Prism `MM_le_of_le` / MME `MMObj_restrict_of_le`. -/
private theorem MMObj_restrict_of_le {n n' m m' p p' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hp : p ≤ p') :
    TensorObj.Restrict (MMObj K n m p) (MMObj K n' m' p') := by
  let f₀ : (MMObj K n' m' p').V 0 →ₗ[K] (MMObj K n m p).V 0 :=
    LinearMap.funLeft K K (fun ab : Fin n × Fin m => (Fin.castLE hn ab.1, Fin.castLE hm ab.2))
  let f₁ : (MMObj K n' m' p').V 1 →ₗ[K] (MMObj K n m p).V 1 :=
    LinearMap.funLeft K K (fun ab : Fin m × Fin p => (Fin.castLE hm ab.1, Fin.castLE hp ab.2))
  let f₂ : (MMObj K n' m' p').V 2 →ₗ[K] (MMObj K n m p).V 2 :=
    LinearMap.funLeft K K (fun ab : Fin p × Fin n => (Fin.castLE hp ab.1, Fin.castLE hn ab.2))
  let hf : ∀ s : Fin 3, (MMObj K n' m' p').V s →ₗ[K] (MMObj K n m p).V s :=
    fun s => Fin.cases f₀ (fun s => Fin.cases f₁ (fun s => Fin.cases f₂
      (fun s => absurd s.isLt (by omega)) s) s) s
  refine ⟨hf, ?_⟩
  have key : ∀ (i : Fin n) (j : Fin m) (k : Fin p),
      PiTensorProduct.map hf
        (MMPure K n' m' p' (Fin.castLE hn i) (Fin.castLE hm j) (Fin.castLE hp k)) =
      MMPure K n m p i j k := by
    intro i j k
    simp only [MMPure, hf, f₀, f₁, f₂]
    erw [PiTensorProduct.map_tprod]
    congr 1; funext s; fin_cases s
    · change (LinearMap.funLeft K K _) (Pi.single (Fin.castLE hn i, Fin.castLE hm j) 1) =
        Pi.single (i, j) 1
      funext ⟨a, b⟩; rw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
    · change (LinearMap.funLeft K K _) (Pi.single (Fin.castLE hm j, Fin.castLE hp k) 1) =
        Pi.single (j, k) 1
      funext ⟨a, b⟩; rw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
    · change (LinearMap.funLeft K K _) (Pi.single (Fin.castLE hp k, Fin.castLE hn i) 1) =
        Pi.single (k, i) 1
      funext ⟨a, b⟩; rw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
  have h_out : ∀ (i' : Fin n') (j' : Fin m') (k' : Fin p'),
      (¬ i'.val < n ∨ ¬ j'.val < m ∨ ¬ k'.val < p) →
      PiTensorProduct.map hf (MMPure K n' m' p' i' j' k') = 0 := by
    intro i' j' k' h
    dsimp only [f₀, f₁, f₂, hf, MMPure]
    erw [PiTensorProduct.map_tprod]
    rcases h with h | h | h
    · apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
      show (LinearMap.funLeft K K fun ab : Fin n × Fin m =>
        (Fin.castLE hn ab.1, Fin.castLE hm ab.2)) (Pi.single (i', j') 1) = 0
      funext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      simp only [LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Prod.mk.injEq,
        Fin.ext_iff, Fin.val_castLE]
      split_ifs with hif
      · exact absurd (hif.1 ▸ ha) h
      · rfl
    · apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
      show (LinearMap.funLeft K K fun ab : Fin m × Fin p =>
        (Fin.castLE hm ab.1, Fin.castLE hp ab.2)) (Pi.single (j', k') 1) = 0
      funext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      simp only [LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Prod.mk.injEq,
        Fin.ext_iff, Fin.val_castLE]
      split_ifs with hif
      · exact absurd (hif.1 ▸ ha) h
      · rfl
    · apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
      show (LinearMap.funLeft K K fun ab : Fin p × Fin n =>
        (Fin.castLE hp ab.1, Fin.castLE hn ab.2)) (Pi.single (k', i') 1) = 0
      funext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      simp only [LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Prod.mk.injEq,
        Fin.ext_iff, Fin.val_castLE]
      split_ifs with hif
      · exact absurd (hif.1 ▸ ha) h
      · rfl
  show PiTensorProduct.map hf (MMObj K n' m' p').t = (MMObj K n m p).t
  rw [MMObj_t_eq, MMObj_t_eq]
  have sum_le : ∀ {M : Type u} [AddCommMonoid M] (n1 n2 : ℕ) (h12 : n1 ≤ n2) (f : Fin n2 → M)
      (hf0 : ∀ i : Fin n2, ¬ i.val < n1 → f i = 0),
      ∑ i : Fin n2, f i = ∑ i : Fin n1, f (Fin.castLE h12 i) := by
    intro M _ n1 n2 h12 f hf0
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h12
    rw [Fin.sum_univ_add]
    have tail_zero : ∑ i : Fin d, f (Fin.natAdd n1 i) = 0 :=
      Finset.sum_eq_zero (fun i _ => hf0 _ (by simp [Fin.natAdd]))
    have step : ∑ i : Fin n1, f (Fin.castAdd d i) = ∑ i : Fin n1, f (Fin.castLE h12 i) :=
      Finset.sum_congr rfl fun i _ => by congr 1
    simp [tail_zero, step]
  have step1 :
      ∑ i : Fin n', ∑ j : Fin m', ∑ k : Fin p',
        (PiTensorProduct.map hf) (MMPure K n' m' p' i j k) =
      ∑ i : Fin n, ∑ j : Fin m', ∑ k : Fin p',
        (PiTensorProduct.map hf) (MMPure K n' m' p' (Fin.castLE hn i) j k) :=
    sum_le n n' hn _ (fun i' hi' =>
      Finset.sum_eq_zero (fun j' _ => Finset.sum_eq_zero (fun k' _ => h_out i' j' k' (Or.inl hi'))))
  have step2 : ∀ i : Fin n,
      ∑ j : Fin m', ∑ k : Fin p',
        (PiTensorProduct.map hf) (MMPure K n' m' p' (Fin.castLE hn i) j k) =
      ∑ j : Fin m, ∑ k : Fin p',
        (PiTensorProduct.map hf) (MMPure K n' m' p' (Fin.castLE hn i) (Fin.castLE hm j) k) :=
    fun i => sum_le m m' hm _ (fun j' hj' =>
      Finset.sum_eq_zero (fun k' _ => h_out (Fin.castLE hn i) j' k' (Or.inr (Or.inl hj'))))
  have step3 : ∀ (i : Fin n) (j : Fin m),
      ∑ k : Fin p', (PiTensorProduct.map hf)
        (MMPure K n' m' p' (Fin.castLE hn i) (Fin.castLE hm j) k) =
      ∑ k : Fin p, MMPure K n m p i j k :=
    fun i j => by
      rw [sum_le p p' hp _ (fun k' hk' =>
        h_out (Fin.castLE hn i) (Fin.castLE hm j) k' (Or.inr (Or.inr hk')))]
      apply Finset.sum_congr rfl; intro k _; exact key i j k
  calc PiTensorProduct.map hf
        (∑ i : Fin n', ∑ j : Fin m', ∑ k : Fin p', MMPure K n' m' p' i j k)
      = ∑ i, ∑ j, ∑ k, (PiTensorProduct.map hf) (MMPure K n' m' p' i j k) := by simp only [map_sum]
    _ = ∑ i, ∑ j, ∑ k, (PiTensorProduct.map hf) (MMPure K n' m' p' (Fin.castLE hn i) j k) := step1
    _ = ∑ i, ∑ j, ∑ k, MMPure K n m p i j k := by
        apply Finset.sum_congr rfl; intro i _
        rw [step2]; apply Finset.sum_congr rfl; intro j _
        exact step3 i j

/-- `MMObj n m p` restricts to the diagonal `diagObj K 3 (n*m*p)` (its tensor element is a
sum of `n*m*p` pure tensors). Port of Prism `MM_le_mul` / MME `MMObj_restrict_diag`. -/
private theorem MMObj_restrict_diag (n m p : ℕ) :
    TensorObj.Restrict (MMObj K n m p) (TensorObj.diagObj K 3 (n * m * p)) := by
  let e : Fin (n * m * p) ≃ Fin n × Fin m × Fin p :=
    finProdFinEquiv.symm.trans
      (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _) |>.trans (Equiv.prodAssoc _ _ _))
  -- the family of pure tensors
  set w : Fin (n * m * p) → ∀ s : Fin 3, (MMObj K n m p).V s :=
    fun idx (s : Fin 3) =>
      match s with
      | ⟨0, _⟩ => (Pi.single ((e idx).1, (e idx).2.1) 1 : Fin n × Fin m → K)
      | ⟨1, _⟩ => (Pi.single ((e idx).2.1, (e idx).2.2) 1 : Fin m × Fin p → K)
      | ⟨2, _⟩ => (Pi.single ((e idx).2.2, (e idx).1) 1 : Fin p × Fin n → K) with hw
  have hX : (MMObj K n m p).t = ∑ idx : Fin (n * m * p), tprod K (w idx) := by
    rw [MMObj_t_eq]
    rw [show (∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, MMPure K n m p i j k) =
        ∑ ijk : Fin n × Fin m × Fin p, MMPure K n m p ijk.1 ijk.2.1 ijk.2.2 from by
      simp_rw [← Finset.sum_product']; rfl]
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl (fun idx _ => ?_)
    simp only [Equiv.apply_symm_apply, hw, MMPure]
    rfl
  -- the basis-to-`w` restriction maps
  refine ⟨fun i => ∑ idx : Fin (n * m * p),
    LinearMap.smulRight (LinearMap.proj idx : (Fin (n * m * p) → K) →ₗ[K] K) (w idx i), ?_⟩
  have hf_eval : ∀ (i : Fin 3) (k : Fin (n * m * p)),
      (∑ idx : Fin (n * m * p),
        LinearMap.smulRight (LinearMap.proj idx : (Fin (n * m * p) → K) →ₗ[K] K) (w idx i))
        (Pi.single k (1 : K)) = w k i := by
    intro i k
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      (fun idx _ hidx => by rw [Pi.single_eq_of_ne hidx, zero_smul])]
    simp
  show PiTensorProduct.map _ (TensorObj.diagObj K 3 (n * m * p)).t = (MMObj K n m p).t
  rw [hX]
  show PiTensorProduct.map _
      (∑ idx : Fin (n * m * p),
        PiTensorProduct.tprod K (fun _ => (Pi.single idx 1 : Fin (n * m * p) → K))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun idx _ => ?_)
  rw [PiTensorProduct.map_tprod]
  exact congrArg (PiTensorProduct.tprod K) (funext fun i => hf_eval i idx)

/-! ## Step 1: rank identification

`strassenRank (MMTensor K n n n) = tensorRankObj (MMObj K n n n)`. Both are `sInf` of the
"restricts to the diagonal `I_r`" sets, which coincide because `MMObj.t = MMTensor` and
`diagObj.t = diagTensor` definitionally — exactly the defeq already exploited by
`Def_mme_omega_pos.n_le_strassenRank_MMTensor`. Combining with the concrete↔abstract rank
reconciliation `TensorQ.rank_tensorStrassen_toQ` gives the abstract form. -/

/-- `strassenRank (MMTensor K n m p) = tensorRankObj (MMObj K n m p)`: the two `sInf`-defining
restriction-witness sets coincide definitionally. -/
private theorem strassenRank_MMTensor_eq_tensorRankObj (n m p : ℕ) :
    strassenRank (MMTensor K n m p) = tensorRankObj (MMObj K n m p) :=
  -- both unfold to the same `sInf` of the same restriction-witness set
  -- (`MMObj.t = MMTensor`, `diagObj.t = diagTensor`, `Restrict = TensorObj.Restrict`).
  rfl

/-- **Rank identification (abstract form).** The Strassen rank of `MM(n,n,n)` equals the
abstract rank of `toQ (MMObj n n n)` in the canonical preorder. -/
private theorem strassenRank_MMTensor_eq_rank (n : ℕ) :
    strassenRank (MMTensor K n n n) =
      StrassenPreorder.rank (Pcan K) (TensorQ.toQ (MMObj K n n n)) := by
  rw [strassenRank_MMTensor_eq_tensorRankObj,
    TensorQ.rank_tensorStrassen_toQ hd3 (MMObj K n n n)]

/-! ## Step 2: powers of the canonical MM element -/

/-- `kronPow (MMObj K n n n) k ≅ MMObj K (n^k) (n^k) (n^k)`. Iterating `MMObj_kron_iso`,
with the `oneObj ≅ MMObj 1 1 1` base case. -/
private theorem MMObj_kronPow_iso (n k : ℕ) :
    TensorObj.Isomorphic (TensorObj.kronPow (MMObj K n n n) k)
      (MMObj K (n ^ k) (n ^ k) (n ^ k)) := by
  induction k with
  | zero =>
    -- `kronPow X 0 = oneObj`; `oneObj ≅ MMObj 1 1 1`.
    show TensorObj.Isomorphic TensorObj.oneObj (MMObj K 1 1 1)
    -- per-mode `K → (Fin 1 × Fin 1 → K)` and back
    let toMM : ∀ s : Fin 3, (TensorObj.oneObj : TensorObj K 3).V s →ₗ[K] (MMObj K 1 1 1).V s :=
      fun s => Fin.cases (LinearMap.smulRight (1 : K →ₗ[K] K) (Pi.single (0, 0) 1))
        (fun s => Fin.cases (LinearMap.smulRight (1 : K →ₗ[K] K) (Pi.single (0, 0) 1))
          (fun s => Fin.cases (LinearMap.smulRight (1 : K →ₗ[K] K) (Pi.single (0, 0) 1))
            (fun s => absurd s.isLt (by omega)) s) s) s
    let toOne : ∀ s : Fin 3, (MMObj K 1 1 1).V s →ₗ[K] (TensorObj.oneObj : TensorObj K 3).V s :=
      fun s => Fin.cases (LinearMap.proj (0, 0))
        (fun s => Fin.cases (LinearMap.proj (0, 0))
          (fun s => Fin.cases (LinearMap.proj (0, 0))
            (fun s => absurd s.isLt (by omega)) s) s) s
    refine ⟨?_, ?_⟩
    · -- Restrict oneObj (MMObj 1 1 1)
      refine ⟨toOne, ?_⟩
      show PiTensorProduct.map _ (MMObj K 1 1 1).t = (TensorObj.oneObj : TensorObj K 3).t
      rw [MMObj_t_eq, Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_one]
      show PiTensorProduct.map toOne (MMPure K 1 1 1 0 0 0) = tprod K (fun _ => (1 : K))
      simp only [MMPure]
      erw [PiTensorProduct.map_tprod]
      congr 1; funext s; fin_cases s <;>
        · change (LinearMap.proj (0, 0)) (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) = 1
          rw [LinearMap.proj_apply, Pi.single_eq_same]
    · -- Restrict (MMObj 1 1 1) oneObj
      refine ⟨toMM, ?_⟩
      show PiTensorProduct.map _ (TensorObj.oneObj : TensorObj K 3).t = (MMObj K 1 1 1).t
      show PiTensorProduct.map toMM (tprod K (fun _ => (1 : K))) = (MMObj K 1 1 1).t
      rw [MMObj_t_eq, Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_one]
      show _ = MMPure K 1 1 1 0 0 0
      simp only [MMPure]
      erw [PiTensorProduct.map_tprod]
      congr 1; funext s; fin_cases s <;>
        · change LinearMap.smulRight (1 : K →ₗ[K] K)
            (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) (1 : K) =
            (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
          simp [LinearMap.smulRight_apply]
  | succ j ih =>
    -- `kronPow X (j+1) = kron X (kronPow X j)`; chain the iso with `MMObj_kron_iso`.
    show TensorObj.Isomorphic
      (TensorObj.kron (MMObj K n n n) (TensorObj.kronPow (MMObj K n n n) j))
      (MMObj K (n ^ (j + 1)) (n ^ (j + 1)) (n ^ (j + 1)))
    have hkron : TensorObj.Isomorphic
        (TensorObj.kron (MMObj K n n n) (TensorObj.kronPow (MMObj K n n n) j))
        (TensorObj.kron (MMObj K n n n) (MMObj K (n ^ j) (n ^ j) (n ^ j))) :=
      TensorQ.mul_respects_iso (TensorObj.Isomorphic.refl _) ih
    refine hkron.trans ?_
    have hmul := MMObj_kron_iso (K := K) n n n (n ^ j) (n ^ j) (n ^ j)
    rw [show n * n ^ j = n ^ (j + 1) from by rw [pow_succ]; ring] at hmul
    exact hmul

/-- `toQ (MMObj K 2 2 2) ^ k = toQ (MMObj K (2^k) (2^k) (2^k))`. -/
private theorem Mq_pow (k : ℕ) :
    (TensorQ.toQ (MMObj K 2 2 2)) ^ k = TensorQ.toQ (MMObj K (2 ^ k) (2 ^ k) (2 ^ k)) := by
  rw [← TensorQ.toQ_kronPow]
  exact TensorQ.toQ_eq_iff.mpr (MMObj_kronPow_iso 2 k)

/-- `rank Pcan 0 = 0`. -/
private theorem rank_Pcan_zero : StrassenPreorder.rank (Pcan K) (0 : TensorQ K 3) = 0 :=
  Nat.le_zero.mp (StrassenPreorder.rank_le_of_le (Pcan K)
    (by rw [Nat.cast_zero]; exact (Pcan K).zero_le 0))

/-- The canonical MM element `toQ (MMObj K 2 2 2)` is nonzero. Its abstract rank equals
`strassenRank (MMTensor 2 2 2) ≥ 2 > 0`, while `rank 0 = 0`. -/
private theorem Mq_ne_zero : (TensorQ.toQ (MMObj K 2 2 2)) ≠ 0 := by
  intro h
  have hrank : StrassenPreorder.rank (Pcan K) (TensorQ.toQ (MMObj K 2 2 2)) =
      strassenRank (MMTensor K 2 2 2) := (strassenRank_MMTensor_eq_rank 2).symm
  have h2 : 2 ≤ strassenRank (MMTensor K 2 2 2) := n_le_strassenRank_MMTensor 2
  rw [h, rank_Pcan_zero] at hrank
  omega

/-! ## Step 3: the analytic core (Fekete / squeeze), ported from Prism

`matMulExp_strassen K = Real.log (asymptoticRank Pcan M) / Real.log 2` where
`M = toQ (MMObj K 2 2 2)`. Combined with the asymptotic-rank bridge
`tensorAsymptoticRank_eq` this gives the target. -/

/-- Abstract form of the matrix-multiplication exponent: rewrite each `strassenRank`
summand via `strassenRank_MMTensor_eq_rank`. -/
private theorem matMulExp_strassen_eq_abstract :
    matMulExp_strassen K =
      iInf (fun n : ℕ => if 1 < n then
        Real.log (StrassenPreorder.rank (Pcan K) (TensorQ.toQ (MMObj K n n n)) : ℝ) /
          Real.log n else 3) := by
  rw [matMulExp_strassen]
  refine iInf_congr (fun n => ?_)
  split_ifs with hn
  · rw [strassenRank_MMTensor_eq_rank]
  · rfl

/-- The defining family of `matMulExp_strassen` (abstract form). -/
private noncomputable def mmFun (n : ℕ) : ℝ :=
  if 1 < n then
    Real.log (StrassenPreorder.rank (Pcan K) (TensorQ.toQ (MMObj K n n n)) : ℝ) / Real.log n
  else 3

private theorem mmFun_nonneg (n : ℕ) : 0 ≤ mmFun (K := K) n := by
  unfold mmFun
  split_ifs with hn
  · refine div_nonneg ?_ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    refine Real.log_nonneg ?_
    have : 1 ≤ StrassenPreorder.rank (Pcan K) (TensorQ.toQ (MMObj K n n n)) := by
      rw [← strassenRank_MMTensor_eq_rank]
      exact le_trans (by omega) (n_le_strassenRank_MMTensor n)
    exact_mod_cast this
  · norm_num

private theorem mmFun_bddBelow : BddBelow (Set.range (mmFun (K := K))) := by
  refine ⟨0, ?_⟩; rintro _ ⟨n, rfl⟩; exact mmFun_nonneg n

private theorem matMulExp_strassen_le_at {n : ℕ} (hn : 1 < n) :
    matMulExp_strassen K ≤
      Real.log (StrassenPreorder.rank (Pcan K) (TensorQ.toQ (MMObj K n n n)) : ℝ) /
        Real.log n := by
  rw [matMulExp_strassen_eq_abstract]
  have h := ciInf_le (mmFun_bddBelow (K := K)) n
  unfold mmFun at h
  rw [if_pos hn] at h
  exact h

/-- `1 ≤ rank Pcan (toQ (MMObj n m p))` for positive dimensions. -/
private theorem one_le_rank_MMq {n m p : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    1 ≤ StrassenPreorder.rank (Pcan K) (TensorQ.toQ (MMObj K n m p)) := by
  refine StrassenPreorder.one_le_rank_of_ne_zero (Pcan K) ?_
  intro h
  -- `1 = toQ (MMObj 1 1 1) ≤ toQ (MMObj n m p) = 0`, contradicting nat_order_embedding
  have hone : (1 : TensorQ K 3) = TensorQ.toQ (MMObj K 1 1 1) := by
    have := Mq_pow (K := K) 0; simpa using this
  have hle : (Pcan K).le (TensorQ.toQ (MMObj K 1 1 1)) (TensorQ.toQ (MMObj K n m p)) :=
    (TensorQ.le_toQ (MMObj K 1 1 1) (MMObj K n m p)).mpr (MMObj_restrict_of_le hn hm hp)
  rw [← hone, h] at hle
  have h1' : (Pcan K).le ((1 : ℕ) : TensorQ K 3) ((0 : ℕ) : TensorQ K 3) := by
    rw [Nat.cast_one, Nat.cast_zero]; exact hle
  exact Nat.not_succ_le_zero 0 (((Pcan K).nat_order_embedding 1 0).mp h1')

/-- **Normalization (abstract form).** The Strassen-form matrix-multiplication exponent
equals `log₂` of the abstract asymptotic rank of `M = toQ (MMObj 2 2 2)`. Port of Prism
`matMulExp_eq_log_AR_222`. -/
private theorem matMulExp_strassen_eq_log_asymptoticRank_abstract :
    matMulExp_strassen K =
      Real.log (StrassenPreorder.asymptoticRank (Pcan K) (TensorQ.toQ (MMObj K 2 2 2))) /
        Real.log 2 := by
  set P : StrassenPreorder (TensorQ K 3) := Pcan K with hP
  set M : TensorQ K 3 := TensorQ.toQ (MMObj K 2 2 2) with hM
  have hM_ne : M ≠ 0 := Mq_ne_zero
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the Fekete convergence `rank(Mᵏ)^(1/k) → asymptoticRank P M`
  have hAR : Tendsto
      (fun k : ℕ => (StrassenPreorder.rank P (M ^ k) : ℝ) ^ (1 / (k : ℝ)))
      atTop (nhds (StrassenPreorder.asymptoticRank P M)) :=
    StrassenPreorder.tends_to_asymptoticRank P hM_ne
  -- `M ^ k = toQ (MMObj (2^k) (2^k) (2^k))`
  have hpow : ∀ k : ℕ, M ^ k = TensorQ.toQ (MMObj K (2 ^ k) (2 ^ k) (2 ^ k)) := fun k => Mq_pow k
  -- `rank P (M^k) ≥ 1` (k ≥ 1)
  have hrank_pow_ge1 : ∀ k : ℕ, 1 ≤ k → 1 ≤ (StrassenPreorder.rank P (M ^ k) : ℝ) := by
    intro k hk
    rw [hpow k]
    have : 1 ≤ StrassenPreorder.rank P (TensorQ.toQ (MMObj K (2 ^ k) (2 ^ k) (2 ^ k))) :=
      one_le_rank_MMq Nat.one_le_two_pow Nat.one_le_two_pow Nat.one_le_two_pow
    exact_mod_cast this
  -- `asymptoticRank P M > 0`
  have hAR_pos : 0 < StrassenPreorder.asymptoticRank P M := by
    have h_eventually : ∀ᶠ k : ℕ in atTop,
        (1 : ℝ) ≤ (StrassenPreorder.rank P (M ^ k) : ℝ) ^ (1 / (k : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      calc (1 : ℝ) = (1 : ℝ) ^ (1 / (k : ℝ)) := by rw [Real.one_rpow]
        _ ≤ _ := Real.rpow_le_rpow (by norm_num) (hrank_pow_ge1 k hk) (by positivity)
    linarith [ge_of_tendsto hAR h_eventually]
  refine le_antisymm ?_ ?_
  · -- forward: `ω ≤ log₂ AR`
    have hLog : Tendsto
        (fun k : ℕ => Real.log ((StrassenPreorder.rank P (M ^ k) : ℝ) ^ (1 / (k : ℝ))))
        atTop (nhds (Real.log (StrassenPreorder.asymptoticRank P M))) :=
      (Real.continuousAt_log (ne_of_gt hAR_pos)).tendsto.comp hAR
    have hLog_eq : ∀ᶠ k : ℕ in atTop,
        Real.log ((StrassenPreorder.rank P (M ^ k) : ℝ) ^ (1 / (k : ℝ))) =
        Real.log (StrassenPreorder.rank P (M ^ k) : ℝ) / k := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hrk_pos : (0 : ℝ) < (StrassenPreorder.rank P (M ^ k) : ℝ) :=
        lt_of_lt_of_le one_pos (hrank_pow_ge1 k hk)
      rw [Real.log_rpow hrk_pos]; ring
    have hLog' : Tendsto
        (fun k : ℕ => Real.log (StrassenPreorder.rank P (M ^ k) : ℝ) / k)
        atTop (nhds (Real.log (StrassenPreorder.asymptoticRank P M))) :=
      hLog.congr' hLog_eq
    have hLog_div : Tendsto
        (fun k : ℕ => Real.log (StrassenPreorder.rank P (M ^ k) : ℝ) /
          ((k : ℝ) * Real.log 2))
        atTop (nhds (Real.log (StrassenPreorder.asymptoticRank P M) / Real.log 2)) := by
      refine (hLog'.div_const (Real.log 2)).congr (fun k => ?_)
      rw [div_div]
    refine ge_of_tendsto hLog_div ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have h2k : 1 < 2 ^ k := by
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk; omega
    have h_apply := matMulExp_strassen_le_at (K := K) (n := 2 ^ k) h2k
    have hlog_pow : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
      push_cast; rw [Real.log_pow]
    rw [hlog_pow, ← hpow k] at h_apply
    exact h_apply
  · -- reverse: `log₂ AR ≤ ω`
    rw [matMulExp_strassen_eq_abstract]
    refine le_ciInf ?_
    intro n
    by_cases hn : 1 < n
    · simp only [if_pos hn]
      set N : TensorQ K 3 := TensorQ.toQ (MMObj K n n n) with hN
      have hrN_ge_1 : 1 ≤ StrassenPreorder.rank P N := one_le_rank_MMq
        (by omega) (by omega) (by omega)
      have hrN_pos : (0 : ℝ) < (StrassenPreorder.rank P N : ℝ) := by
        have : (0 : ℕ) < StrassenPreorder.rank P N := by omega
        exact_mod_cast this
      have hlogn_pos : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
      rw [div_le_div_iff₀ hlog2_pos hlogn_pos]
      suffices h_pow : StrassenPreorder.asymptoticRank P M ≤
          (StrassenPreorder.rank P N : ℝ) ^ (Real.log 2 / Real.log n) by
        have h_log := Real.log_le_log hAR_pos h_pow
        rw [Real.log_rpow hrN_pos] at h_log
        have hmul := mul_le_mul_of_nonneg_right
          (show Real.log (StrassenPreorder.asymptoticRank P M) ≤
            Real.log 2 / Real.log n * Real.log (StrassenPreorder.rank P N : ℝ) from h_log)
          (le_of_lt hlogn_pos)
        have hsimp : Real.log 2 / Real.log n * Real.log (StrassenPreorder.rank P N : ℝ) *
            Real.log n = Real.log (StrassenPreorder.rank P N : ℝ) * Real.log 2 := by field_simp
        rw [hsimp] at hmul
        linarith
      -- the squeeze along the subsequence `φ k = ⌈k·α⌉` with `α = log 2 / log n`
      set α : ℝ := Real.log 2 / Real.log n with hα
      have hα_pos : 0 < α := div_pos hlog2_pos hlogn_pos
      let φ : ℕ → ℕ := fun k => ⌈(k : ℝ) * α⌉₊
      have hφ_ge : ∀ k : ℕ, (k : ℝ) * α ≤ φ k := fun k => Nat.le_ceil _
      have hn_pow_ge_nat : ∀ k : ℕ, 2 ^ k ≤ n ^ (φ k) := by
        intro k
        have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have h2 : (k : ℝ) * Real.log 2 ≤ (φ k : ℝ) * Real.log n := by
          have hineq : (k : ℝ) * α * Real.log n ≤ (φ k : ℝ) * Real.log n :=
            mul_le_mul_of_nonneg_right (hφ_ge k) (le_of_lt hlogn_pos)
          have heq : (k : ℝ) * α * Real.log n = (k : ℝ) * Real.log 2 := by rw [hα]; field_simp
          linarith
        have hge : (2 : ℝ) ^ k ≤ (n : ℝ) ^ (φ k) := by
          rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          exact h2
        exact_mod_cast hge
      -- `rank P (M^k) ≤ rank P (N^(φ k)) ≤ (rank P N)^(φ k)`
      have h_le_canon : ∀ k : ℕ,
          StrassenPreorder.rank P (M ^ k) ≤ StrassenPreorder.rank P (N ^ (φ k)) := by
        intro k
        apply StrassenPreorder.rank_monotone
        rw [hpow k]
        rw [show (N ^ (φ k) : TensorQ K 3) =
            TensorQ.toQ (MMObj K (n ^ (φ k)) (n ^ (φ k)) (n ^ (φ k))) from by
          rw [hN, ← TensorQ.toQ_kronPow]
          apply TensorQ.toQ_eq_iff.mpr
          exact MMObj_kronPow_iso n (φ k)]
        exact (TensorQ.le_toQ _ _).mpr
          (MMObj_restrict_of_le (hn_pow_ge_nat k) (hn_pow_ge_nat k) (hn_pow_ge_nat k))
      have h_rank_N_pow : ∀ k : ℕ,
          StrassenPreorder.rank P (N ^ (φ k)) ≤ (StrassenPreorder.rank P N) ^ (φ k) := by
        intro k
        induction φ k with
        | zero => rw [pow_zero, pow_zero, StrassenPreorder.rank_one]
        | succ j ih =>
          rw [pow_succ, pow_succ]
          calc StrassenPreorder.rank P (N ^ j * N)
              ≤ StrassenPreorder.rank P (N ^ j) * StrassenPreorder.rank P N :=
                StrassenPreorder.rank_submultiplicative _ _ _
            _ ≤ (StrassenPreorder.rank P N) ^ j * StrassenPreorder.rank P N :=
                Nat.mul_le_mul_right _ ih
      have h_combined : ∀ k : ℕ,
          (StrassenPreorder.rank P (M ^ k) : ℝ) ≤ (StrassenPreorder.rank P N : ℝ) ^ (φ k) := by
        intro k
        have : StrassenPreorder.rank P (M ^ k) ≤ (StrassenPreorder.rank P N) ^ (φ k) :=
          le_trans (h_le_canon k) (h_rank_N_pow k)
        exact_mod_cast this
      -- `φ k / k → α`
      have hφ_div_tend : Tendsto (fun k : ℕ => (φ k : ℝ) / k) atTop (nhds α) := by
        have h_ub : ∀ k : ℕ, (φ k : ℝ) < (k : ℝ) * α + 1 := by
          intro k
          have hk_α_nn : 0 ≤ (k : ℝ) * α := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hα_pos)
          exact_mod_cast Nat.ceil_lt_add_one hk_α_nn
        have h_α_le : ∀ᶠ k : ℕ in atTop, α ≤ (φ k : ℝ) / k := by
          filter_upwards [eventually_ge_atTop 1] with k hk
          have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hk
          rw [le_div_iff₀ hkR_pos]; linarith [hφ_ge k]
        have h_lt_α_plus : ∀ᶠ k : ℕ in atTop, (φ k : ℝ) / k < α + 1 / k := by
          filter_upwards [eventually_ge_atTop 1] with k hk
          have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hk
          rw [div_lt_iff₀ hkR_pos]
          have heq : (α + 1 / (k : ℝ)) * k = α * k + 1 := by field_simp
          rw [heq]; linarith [h_ub k]
        have h_α_plus : Tendsto (fun k : ℕ => α + 1 / (k : ℝ)) atTop (nhds α) := by
          have := (tendsto_const_nhds (x := α)).add
            (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
          simpa using this
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_α_plus
          h_α_le (h_lt_α_plus.mono fun _ h => le_of_lt h)
      have h_continuous_rpow : Tendsto
          (fun k : ℕ => (StrassenPreorder.rank P N : ℝ) ^ ((φ k : ℝ) / k))
          atTop (nhds ((StrassenPreorder.rank P N : ℝ) ^ α)) :=
        (Real.continuousAt_const_rpow (ne_of_gt hrN_pos)).tendsto.comp hφ_div_tend
      have h_le_each : ∀ᶠ k : ℕ in atTop,
          (StrassenPreorder.rank P (M ^ k) : ℝ) ^ (1 / (k : ℝ)) ≤
          (StrassenPreorder.rank P N : ℝ) ^ ((φ k : ℝ) / k) := by
        filter_upwards [eventually_ge_atTop 1] with k hk
        have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
        have h1 : (StrassenPreorder.rank P (M ^ k) : ℝ) ^ (1 / (k : ℝ)) ≤
            ((StrassenPreorder.rank P N : ℝ) ^ (φ k : ℕ)) ^ (1 / (k : ℝ)) := by
          refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by positivity)
          rw [show ((StrassenPreorder.rank P N : ℝ) ^ (φ k : ℕ)) =
            (StrassenPreorder.rank P N : ℝ) ^ (φ k) from by norm_cast]
          exact h_combined k
        have h2 : ((StrassenPreorder.rank P N : ℝ) ^ (φ k : ℕ)) ^ (1 / (k : ℝ)) =
            (StrassenPreorder.rank P N : ℝ) ^ ((φ k : ℝ) / k) := by
          rw [← Real.rpow_natCast (StrassenPreorder.rank P N : ℝ) (φ k),
            ← Real.rpow_mul (le_of_lt hrN_pos)]
          congr 1; field_simp
        rw [← h2]; exact h1
      exact le_of_tendsto_of_tendsto hAR h_continuous_rpow h_le_each
    · -- `n ≤ 1` branch: `asymptoticRank ≤ 8 = 2^3`
      simp only [if_neg hn]
      -- `M ≤ 8` since `MMObj 2 2 2 ≤ I_8`
      have hM_le_8 : P.le M ((8 : ℕ) : TensorQ K 3) := by
        have h := MMObj_restrict_diag (K := K) 2 2 2
        rw [show (2 * 2 * 2 : ℕ) = 8 from rfl] at h
        rw [hM, hP, show ((8 : ℕ) : TensorQ K 3) = TensorQ.toQ (TensorObj.diagObj K 3 8) from
          TensorQ.natCast_eq 8]
        exact (TensorQ.le_toQ _ _).mpr h
      have hrank_natCast : ∀ j : ℕ, StrassenPreorder.rank P ((j : TensorQ K 3)) ≤ j := by
        intro j
        exact StrassenPreorder.rank_le_of_le P (P.le_refl _)
      have hrank_M_le_8 : StrassenPreorder.rank P M ≤ 8 :=
        le_trans (StrassenPreorder.rank_monotone P hM_le_8) (hrank_natCast 8)
      have hrank_pow : ∀ k : ℕ, StrassenPreorder.rank P (M ^ k) ≤ 8 ^ k := by
        intro k
        induction k with
        | zero => rw [pow_zero, pow_zero, StrassenPreorder.rank_one]
        | succ k ih =>
          rw [pow_succ, pow_succ]
          calc StrassenPreorder.rank P (M ^ k * M)
              ≤ StrassenPreorder.rank P (M ^ k) * StrassenPreorder.rank P M :=
                StrassenPreorder.rank_submultiplicative _ _ _
            _ ≤ 8 ^ k * 8 := Nat.mul_le_mul ih hrank_M_le_8
      have hAR_le_8 : StrassenPreorder.asymptoticRank P M ≤ 8 := by
        refine le_of_tendsto_of_tendsto hAR tendsto_const_nhds ?_
        filter_upwards [eventually_ge_atTop 1] with k hk
        have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
        have h1 : ((StrassenPreorder.rank P (M ^ k)) : ℝ) ≤ ((8 ^ k : ℕ) : ℝ) := by
          exact_mod_cast hrank_pow k
        have h_step : (StrassenPreorder.rank P (M ^ k) : ℝ) ^ (1 / (k : ℝ)) ≤
            ((8 ^ k : ℕ) : ℝ) ^ (1 / (k : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by positivity)
        rw [show ((8 ^ k : ℕ) : ℝ) = (8 : ℝ) ^ k from by push_cast; rfl,
          show (8 : ℝ) ^ k = (8 : ℝ) ^ (k : ℝ) from by rw [Real.rpow_natCast],
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 8)] at h_step
        rwa [show (k : ℝ) * (1 / (k : ℝ)) = 1 from by field_simp, Real.rpow_one] at h_step
      have h_log_le : Real.log (StrassenPreorder.asymptoticRank P M) ≤ Real.log 8 :=
        Real.log_le_log hAR_pos hAR_le_8
      have h_log8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]; ring
      rw [h_log8] at h_log_le
      rw [div_le_iff₀ hlog2_pos]; linarith

/-- **PRIMARY RESULT.** ω equals `log₂` of the asymptotic tensor rank of the 2×2×2
matrix-multiplication tensor. -/
theorem matMulExp_strassen_eq_log_AR :
    matMulExp_strassen K =
      Real.log (tensorAsymptoticRank (MMObj K 2 2 2)) / Real.log 2 := by
  rw [matMulExp_strassen_eq_log_asymptoticRank_abstract,
    TensorQ.tensorAsymptoticRank_eq hd3 (MMObj K 2 2 2)]

end MME


