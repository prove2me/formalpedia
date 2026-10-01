-- Prove2me | solution 1 for mme_mixed_depth_regional_boundary_profile_compiler
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T09:42:51.15563+00:00
-- url     : https://prove2.me/submissions/ce57560e-0d2a-4a93-a916-3a66d85e8119

import Definitions.Def_mme_mixed_depth_profile_certificate
import Theorems.Thm_mme_regional_fixed_parent_window_square_stage
import Theorems.Thm_mme_regional_supported_histograms_of_joint_certificate
import Theorems.Thm_mme_elementary_supported_stage_exact_volume
import Theorems.Thm_mme_boundary_scaled_volume_rate

open BigOperators Filter MME MME.RecursiveYZ MME.RegionRealization MME.ProfileCompiler
  MME.ProfiledCW MME.CompleteSplit MME.RecursiveYZ.CWCells MME.MixedCompiler
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000

private def replica {ell L : ℕ} (B : Boundary.Profile ell L) (t : ℕ) :
    Boundary.Profile ell (L * t) where
  index := B.index
  index_le := B.index_le
  count := fun w ↦ B.count w * t
  total := by rw [← Finset.sum_mul, B.total]
  supported := fun w h ↦ B.supported w (mul_ne_zero_iff.mp h).1

private theorem replica_mu {ell L : ℕ} (B : Boundary.Profile ell L) (t : ℕ)
    (z i : Fin 3) (w : CompleteWord ell) :
    (replica B t).mu z i w = B.mu z i w * t := by
  have hz : z = 0 ∨ z = 1 ∨ z = 2 := by omega
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hz with rfl | rfl | rfl <;> rcases hi with rfl | rfl | rfl
  all_goals simp [Boundary.Profile.mu, replica]
  all_goals split_ifs <;> simp

private theorem profile_positive {ell L : ℕ} (B : Boundary.Profile ell L) : 1 ≤ B.dim := by
  have hm := Nat.multinomial_pos Finset.univ B.count
  have h : 0 < L.factorial / ∏ w, (B.count w).factorial := by
    simpa only [Nat.multinomial, B.total] using hm
  exact Nat.mul_pos h (pow_pos (by decide) _)

private theorem profile_oriented_positive {ell L : ℕ} (B : Boundary.Profile ell L)
    (z : Fin 3) : 1 ≤ B.a z ∧ 1 ≤ B.b z ∧ 1 ≤ B.c z := by
  have h := profile_positive B
  simp only [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]
  split_ifs <;> omega

private theorem profile_volume {ell L : ℕ} (B : Boundary.Profile ell L) (z : Fin 3) :
    B.a z * B.b z * B.c z = B.dim := by
  have hz : z = 0 ∨ z = 1 ∨ z = 2 := by omega
  rcases hz with rfl | rfl | rfl <;>
    simp [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]

private def single_partition (L : ℕ) : CWCells.Partition (fun _ : Fin L ↦ (0 : Fin 1)) where
  parts := 1
  cells := Equiv.refl _
  size := fun _ ↦ L
  fiber := fun j ↦ {
    toFun := fun p ↦ ⟨p, Subsingleton.elim _ _⟩
    invFun := Subtype.val
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

private def leaf_source {ell L : ℕ} (B : Boundary.Profile ell L) (z : Fin 3)
    (eps : ℝ) (k : ℕ) : Predicate (L * k ^ 2 * 2 ^ (ell - 1)) := fun i x ↦
  (∀ p, grade (split (Equiv.refl _) rfl x p) = B.shape z i) ∧
    ∀ w, |(count (fun _ : Fin (L * k ^ 2) ↦ ())
      (split (Equiv.refl _) rfl x) () w : ℝ) / (k ^ 2 : ℕ) - (B.mu z i w : ℝ)| < eps

private theorem boundary_leaf {ell L : ℕ} (B : Boundary.Profile ell L) (z : Fin 3)
    (eps : ℝ) (heps : 0 < eps) (k : ℕ) (hk : 0 < k) :
    ∃ E : LogJointRecipeG (L * k ^ 2 * 2 ^ (ell - 1)) ell (leaf_source B z eps k),
      E.inputs = 1 ∧ E.logOutputs = 0 ∧
      1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
      E.a * E.b * E.c = (replica B (k ^ 2)).dim := by
  classical
  let C := replica B (k ^ 2)
  have hkR : (0 : ℝ) < (k ^ 2 : ℕ) := by exact_mod_cast pow_pos hk 2
  let terminal : BoundaryEnd ell (L * k ^ 2 * 2 ^ (ell - 1)) (leaf_source B z eps k) := {
    L := L * k ^ 2
    cells := 1
    length := rfl
    cell := fun _ ↦ 0
    shape := fun _ ↦ C.shape z
    mu := fun i _ ↦ C.mu z i
    partition := single_partition _
    profile := fun _ ↦ C
    zeroMode := fun _ ↦ z
    shapes := by intros; rfl
    profiles := by intros; rfl
    inside := by
      intro i x hx
      refine ⟨hx.1, ?_⟩
      intro w
      have hc : count (fun _ : Fin (L * k ^ 2) ↦ ())
          (split (Equiv.refl _) rfl x) () w = C.mu z i w := by
        simpa only [count, true_and, and_true, eq_self] using hx.2 0 w
      rw [hc]
      change |((replica B (k ^ 2)).mu z i w : ℝ) / (k ^ 2 : ℕ) - (B.mu z i w : ℝ)| < eps
      rw [replica_mu, Nat.cast_mul, mul_div_cancel_right₀ _ hkR.ne']
      simpa only [sub_self, abs_zero] using heps }
  let E : LogJointRecipeG _ ell (leaf_source B z eps k) := .base (.boundary terminal)
  have ha : E.a = C.a z := by simp [E, terminal, BoundaryEnd.a, single_partition,
    LogJointRecipeG.a, LogJointRecipeG.dims, LogRecipe.dims, Fin.prod_univ_one]
  have hb : E.b = C.b z := by simp [E, terminal, BoundaryEnd.b, single_partition,
    LogJointRecipeG.b, LogJointRecipeG.dims, LogRecipe.dims, Fin.prod_univ_one]
  have hc : E.c = C.c z := by simp [E, terminal, BoundaryEnd.c, single_partition,
    LogJointRecipeG.c, LogJointRecipeG.dims, LogRecipe.dims, Fin.prod_univ_one]
  refine ⟨E, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [E, LogJointRecipeG.logOutputs, LogRecipe.logOutputs]
  · simpa only [ha] using (profile_oriented_positive C z).1
  · simpa only [hb] using (profile_oriented_positive C z).2.1
  · simpa only [hc] using (profile_oriented_positive C z).2.2
  · rw [ha, hb, hc, profile_volume]

private theorem zero_profile_dim {ell L : ℕ} (B : Boundary.Profile ell L)
    (hL : L = 0) : B.dim = 1 := by
  classical
  have hz (w : CompleteWord ell) : B.count w = 0 := by
    have h : B.count w ≤ 0 := calc
      _ ≤ ∑ s, B.count s := Finset.single_le_sum
        (fun s _ ↦ Nat.zero_le (B.count s)) (Finset.mem_univ w)
      _ = L := B.total
      _ = 0 := hL
    omega
  simp [Boundary.Profile.dim, hz, hL]

private noncomputable def leaf_rate {ell L : ℕ} (B : Boundary.Profile ell L) : ℝ :=
  if L = 0 then 0 else (L : ℝ) * Real.log 2 *
    mme_modern_entropyBits (fun w ↦ (B.count w : ℝ) / L) +
    ((∑ w, B.count w * Boundary.ones w : ℕ) : ℝ) * Real.log 5

private theorem boundary_leaf_rate {ell L : ℕ} (B : Boundary.Profile ell L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      (k ^ 2 : ℝ) * (leaf_rate B - delta) ≤ Real.log ((replica B (k ^ 2)).dim : ℝ) := by
  by_cases hL : L = 0
  · subst L
    refine ⟨0, ?_⟩
    intro k _
    rw [zero_profile_dim (replica B (k ^ 2)) (by simp)]
    simp [leaf_rate]
    exact mul_nonneg (sq_nonneg _) hd.le
  · have hLp : 0 < L := by omega
    obtain ⟨t0, ht⟩ := eventually_atTop.mp (mme_boundary_scaled_volume_rate B hLp delta hd)
    refine ⟨t0, ?_⟩
    intro k hk
    have hkk : k ≤ k ^ 2 := by nlinarith
    have h := ht (k ^ 2) (hk.trans hkk) (replica B (k ^ 2)) (fun _ ↦ rfl)
    simpa only [leaf_rate, if_neg hL, Nat.cast_pow] using h

private theorem mixed_partition_log_volume {p : ℕ} (a b c : Fin p → ℕ)
    (ha : ∀ j, 1 ≤ a j) (hb : ∀ j, 1 ≤ b j) (hc : ∀ j, 1 ≤ c j) :
    Real.log (((∏ j, a j) * (∏ j, b j) * (∏ j, c j) : ℕ) : ℝ) =
      ∑ j, Real.log ((a j * b j * c j : ℕ) : ℝ) := by
  classical
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Nat.cast_prod]
  apply Real.log_prod
  intro j _
  have h : 0 < a j * b j * c j := by
    exact Nat.mul_pos (Nat.mul_pos (by have := ha j; omega) (by have := hb j; omega))
      (by have := hc j; omega)
  exact_mod_cast Nat.ne_of_gt h

/-- Finite exact boundary profiles compile into actual terminal recipes and
attain their entropy/letter volume rates at a common square scale. -/
private theorem mme_boundary_profile_layer_eventual_recipe {ell : ℕ} {N : ℕ → ℕ}
    (B : BoundaryLayer ell N) (eps delta : ℝ) (he : 0 < eps) (hd : 0 < delta) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∃ E : LogJointRecipeG (N k) ell (B.window.source eps k),
        E.inputs = 1 ∧ E.logOutputs = 0 ∧
        1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
        (k ^ 2 : ℝ) * (B.volumeRate - delta) ≤
          Real.log ((E.a * E.b * E.c : ℕ) : ℝ) := by
  classical
  let d := delta / (B.parts + 1 : ℕ)
  have hd' : 0 < d := div_pos hd (by positivity)
  choose k0 hk0 using fun j ↦ boundary_leaf_rate (B.profile j) d hd'
  refine ⟨max 1 (Finset.univ.sup k0), ?_⟩
  intro k hk
  have hkpos : 0 < k := by have := (le_max_left _ _).trans hk; omega
  have hr j : (k ^ 2 : ℝ) * (leaf_rate (B.profile j) - d) ≤
      Real.log ((replica (B.profile j) (k ^ 2)).dim : ℝ) :=
    hk0 j k ((Finset.le_sup (f := k0) (Finset.mem_univ j)).trans
      ((le_max_right _ _).trans hk))
  choose E hE using fun j ↦ boundary_leaf (B.profile j) (B.zeroMode j) eps he k hkpos
  let R : LogJointRecipeG (N k) ell (B.window.source eps k) :=
    .partition (fun j ↦ B.length j * k ^ 2 * 2 ^ (ell - 1)) (B.positions k)
      (fun j ↦ leaf_source (B.profile j) (B.zeroMode j) eps k)
      (by
        intro i x h
        exact ⟨fun j ↦ (h j).1, fun o ↦ (h o.1).2 o.2⟩) E
  have ha : 1 ≤ R.a := by
    change 1 ≤ ∏ j, (E j).a
    exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.1)
  have hb : 1 ≤ R.b := by
    change 1 ≤ ∏ j, (E j).b
    exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.2.1)
  have hc : 1 ≤ R.c := by
    change 1 ≤ ∏ j, (E j).c
    exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.2.2.1)
  refine ⟨R, ?_, ?_, ha, hb, hc, ?_⟩
  · change (∏ j, (E j).inputs) = 1
    simp only [fun j ↦ (hE j).1, Finset.prod_const_one]
  · change (∑ j, (E j).logOutputs) = 0
    simp only [fun j ↦ (hE j).2.1, Finset.sum_const_zero]
  · have hlog : Real.log ((R.a * R.b * R.c : ℕ) : ℝ) =
        ∑ j, Real.log ((replica (B.profile j) (k ^ 2)).dim : ℝ) := by
      change Real.log (((∏ j, (E j).a) * (∏ j, (E j).b) * (∏ j, (E j).c) : ℕ) : ℝ) = _
      rw [mixed_partition_log_volume _ _ _
        (fun j ↦ (hE j).2.2.1) (fun j ↦ (hE j).2.2.2.1)
        (fun j ↦ (hE j).2.2.2.2.1)]
      simp only [fun j ↦ (hE j).2.2.2.2.2]
    rw [hlog]
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin B.parts))) ↦ hr j)
    have hrate : (∑ j, leaf_rate (B.profile j)) = B.volumeRate := rfl
    have hloss : (B.parts : ℝ) * d ≤ delta := by
      have heq : d * ((B.parts : ℝ) + 1) = delta := by
        dsimp only [d]
        push_cast
        field_simp
      nlinarith [hd'.le]
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hrate] at hsum
    exact (mul_le_mul_of_nonneg_left (by linarith : B.volumeRate - delta ≤
      B.volumeRate - (B.parts : ℝ) * d) (sq_nonneg (k : ℝ))).trans hsum


private theorem layer_window_source_iff {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N)
    (eps : ℝ) (k : ℕ) (i : Fin 3) (x : FineWord (N k)) :
    (layerWindow L).source eps k i x ↔ L.source eps k i x := by
  constructor
  · intro h j
    exact ⟨h.1 j, fun r w ↦ h.2 ⟨j,r,w⟩⟩
  · intro h
    exact ⟨fun j ↦ (h j).1, fun o ↦ (h o.1).2 o.2.1 o.2.2⟩

private theorem full_cell_fiber {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (r : Fin R)
    (c : MME.RecursiveThinSplit.Split half (parent r)) :
    Fintype.card {p : Position n // fullCell htotal a p = ⟨r,c⟩} =
      MME.RecursiveThinSplit.count (a r) c +
      MME.RecursiveThinSplit.count (a r) (complement (htotal r) c) := by
  classical
  let e : {p : Position n // fullCell htotal a p = ⟨r,c⟩} ≃
      {p : Fin (n r) × Fin 2 //
        (if p.2 = 0 then a r p.1 else complement (htotal r) (a r p.1)) = c} := {
    toFun := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨(t,h), eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun p ↦ ⟨⟨r,p.val⟩, by
      change (⟨r,_⟩ : Cell half R parent) = ⟨r,c⟩
      rw [p.property]⟩
    left_inv := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro p; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  have hc (t : Fin (n r)) : complement (htotal r) (a r t) = c ↔
      a r t = complement (htotal r) c := by
    constructor
    · intro h
      simpa only [complement_complement] using congrArg (complement (htotal r)) h
    · intro h
      rw [h, complement_complement]
  simp only [show (1 : Fin 2) ≠ 0 by decide, 
    MME.RecursiveThinSplit.count, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_add_distrib]
  simp only [ite_true, ite_false, hc]
  congr 1

private theorem histogram_mass {P C W : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (f : P → W) (c : C) :
    ∑ w, count cell f c w = Fintype.card {p : P // cell p = c} := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : cell p = c <;> simp [hp]


private theorem stage_positive {M lower : ℕ}
    {S T : ProfiledCW.Predicate M} (D : LogPartStageG M lower S T) :
    ∀ x : Fin 3 → ProfiledCW.FineWord M,
      ProfiledCW.supported x → (∀ i, T i (x i)) → 1 ≤ D.types := by
  induction D with
  | step types rate hr steps budget inside cover =>
    intro x hs ht
    obtain ⟨j, _, _⟩ := cover x hs ht
    have := j.isLt
    dsimp only [LogPartStageG.types]
    omega
  | rotate D ih =>
    intro x hs ht
    apply ih (fun i ↦ x (cyclicPerm i))
    · intro r
      have := hs r
      change (x 1 r).val + (x 2 r).val + (x 0 r).val = 2
      omega
    · intro i
      simpa only [Equiv.symm_apply_apply] using ht (cyclicPerm i)
  | swap D ih =>
    intro x hs ht
    apply ih (fun i ↦ x (swapFirstTwoPerm i))
    · intro r
      have := hs r
      change (x 1 r).val + (x 0 r).val + (x 2 r).val = 2
      omega
    · intro i
      simpa only [Equiv.symm_apply_apply] using ht (swapFirstTwoPerm i)

private theorem packet_histogram_mass {ell : ℕ} (p : Packet ell) (k : ℕ)
    (x : FineWord (p.size k)) (c : p.Cells) :
    ∑ w, p.histogram k x c w = k ^ 2 * p.mass c := by
  classical
  have ha := (Finset.mem_filter.mp (p.address_valid k)).2
  have hf := full_cell_fiber p.total (p.address k) c.1 c.2
  rw [ha, ha] at hf
  change ∑ w, count _ _ c w = _
  rw [histogram_mass]
  simpa only [Fintype.card_eq_nat_card, Packet.mass, mul_add] using hf

/-- The joint table ensures the stage's cover has an inhabited exact type. -/
private theorem packet_exact_supported {ell : ℕ} (p : Packet ell) (k : ℕ) (hk : 0 < k)
    (delta : ℝ) (hd : 0 ≤ delta) :
    ∃ x : Fin 3 → FineWord (p.size k), supported x ∧ (∀ i, p.target delta k i (x i)) ∧
      ∀ i c w, p.histogram k (x i) c w = k ^ 2 * p.mu i c w := by
  classical
  have hk2 : 0 < k ^ 2 := pow_pos hk _
  have ha := (Finset.mem_filter.mp (p.address_valid k)).2
  obtain ⟨x, hs, hx⟩ := mme_regional_supported_histograms_of_joint_certificate
    p.parent p.total (fun r ↦ k ^ 2 * p.n r) (p.address k)
    (MME.DWZProfiledRegional.positionsAt p.n (k ^ 2)) rfl
    (fun c z ↦ k ^ 2 * p.joint c z) (fun i c w ↦ k ^ 2 * p.mu i c w)
    (by
      intro c
      rw [← Finset.mul_sum, p.joint_mass]
      have hf := full_cell_fiber p.total (p.address k) c.1 c.2
      rw [ha, ha] at hf
      simpa only [Fintype.card_eq_nat_card, mul_add] using hf.symm)
    (by intro c z hz; exact p.joint_support c z (by nlinarith))
    (by intro c z hz; exact p.joint_grade c z (by nlinarith))
    (by
      intro i c w
      rw [← Finset.mul_sum]
      congr 1
      exact p.joint_marginal i c w)
  refine ⟨x, hs, ?_, ?_⟩
  · intro i
    refine ⟨(hx i).1, ?_, ?_⟩
    · intro c
      apply Finset.sum_congr rfl
      intro w hw
      exact (hx i).2 c w
    · intro c w
      dsimp only [Packet.histogram, Packet.words]
      change |((_ : ℕ) : ℝ) - ((k ^ 2 * p.mu i c w : ℕ) : ℝ)| ≤ _
      rw [(hx i).2 c w, sub_self, abs_zero]
      exact mul_nonneg hd (Nat.cast_nonneg _)
  · exact fun i c w ↦ (hx i).2 c w

private theorem packet_stages {ell : ℕ} (p : Packet ell) (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ D : LogPartStageG (p.size k) ell (p.source eps k) (p.target delta k),
        1 ≤ D.types ∧ D.types ≤ (k + 1) ^ p.degree ∧ D.rate = p.rate * k ^ 2 := by
  classical
  obtain ⟨delta, hd, k0, h⟩ := mme_regional_fixed_parent_window_square_stage
    p.parent p.total p.n p.n_pos p.regions_pos p.m p.m_mass p.mu p.mu_mass
    p.rate eps p.rate_nonneg p.rate_strict heps p.center (by intros; rfl)
  refine ⟨delta, hd, k0, ?_⟩
  intro k hk
  obtain ⟨hkpos, hh⟩ := h k hk
  obtain ⟨D, ht, hr⟩ := hh (p.address k) (p.address_valid k)
  obtain ⟨x, hs, hx, _⟩ := packet_exact_supported p k hkpos delta hd.le
  exact ⟨D, stage_positive D x hs hx, ht, hr⟩

private theorem layer_stages {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : Fin L.parts → ℝ, (∀ j, 0 < delta j) ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ D : ∀ j, LogPartStageG ((L.packet j).size k) ell
        ((L.packet j).source eps k) ((L.packet j).target (delta j) k),
        (∀ j, 1 ≤ (D j).types ∧ (D j).types ≤ (k + 1) ^ (L.packet j).degree) ∧
        (∀ j, (D j).rate = (L.packet j).rate * k ^ 2) := by
  classical
  choose delta hd k0 h using fun j ↦ packet_stages (L.packet j) eps heps
  refine ⟨delta, hd, Finset.univ.sup k0, ?_⟩
  intro k hk
  have h' : ∀ j, ∃ D : LogPartStageG ((L.packet j).size k) ell
      ((L.packet j).source eps k) ((L.packet j).target (delta j) k),
      1 ≤ D.types ∧ D.types ≤ (k + 1) ^ (L.packet j).degree ∧
      D.rate = (L.packet j).rate * k ^ 2 :=
    fun j ↦ h j k ((Finset.le_sup (f := k0) (Finset.mem_univ j)).trans hk)
  choose D hD using h'
  exact ⟨D, fun j ↦ ⟨(hD j).1, (hD j).2.1⟩, fun j ↦ (hD j).2.2⟩


private theorem histogram_one_count {P C : Type} [Fintype P] [Fintype C]
    {L M : ℕ} (cell : P → C) (positions : Fin L ≃ P)
    (length : L * 2 ^ (1 - 1) = M) (x : FineWord M) :
    (∑ c, count cell (split positions length x) c (fun _ ↦ 1)) =
      ∑ r, if x r = 1 then 1 else 0 := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  trans ∑ p, if split positions length x p = (fun _ ↦ 1) then 1 else 0
  · apply Finset.sum_congr rfl
    intro p _
    by_cases h : split positions length x p = (fun _ ↦ 1)
    · simp only [h, and_true, if_true]
      simp [eq_comm]
    · simp only [h, and_false, if_false, Finset.sum_const_zero]
  letI : Unique (Fin (2 ^ (1 - 1))) := by change Unique (Fin 1); infer_instance
  have hdefault : (default : Fin (2 ^ (1 - 1))) = 0 := by
    change (default : Fin 1) = 0
    exact Subsingleton.elim _ _
  let e : P ≃ Fin M := positions.symm.trans
    ((Equiv.prodUnique (Fin L) (Fin (2 ^ (1 - 1)))).symm.trans
      (finProdFinEquiv.trans (finCongr length)))
  apply Fintype.sum_equiv e
  intro p
  have hw : split positions length x p = (fun _ ↦ 1) ↔ x (e p) = 1 := by
    constructor
    · intro h
      simpa [e, split, Equiv.prodUnique_symm_apply, hdefault] using congrFun h 0
    · intro h
      funext r
      have hr : r = 0 := by fin_cases r; rfl
      simpa [hr, e, split, Equiv.prodUnique_symm_apply, hdefault] using h
  simp only [hw]


private theorem terminal_layer {N : ℕ → ℕ} (L : Layer 1 N) (eps : ℝ) (he : 0 < eps) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ E : LogJointRecipeG (N k) 2 ((layerWindow L).source eps k),
      E.inputs = 1 ∧ E.logOutputs = L.rate * k ^ 2 ∧
      1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
      (E.a * E.b * E.c) ^ 2 =
        5 ^ (k ^ 2 * ∑ j, ∑ i : Fin 3, ∑ c, (L.packet j).mu i c (fun _ ↦ 1)) := by
  classical
  obtain ⟨delta, hd, k0, h⟩ := layer_stages L eps he
  refine ⟨max 1 k0, ?_⟩
  intro k hk
  have hkpos : 0 < k := by have := (le_max_left 1 k0).trans hk; omega
  obtain ⟨D, hp, hr⟩ := h k ((le_max_right 1 k0).trans hk)
  have hparts : ∀ j, ∃ E : LogJointRecipeG ((L.packet j).size k) 2
      ((L.packet j).source eps k), E.inputs = 1 ∧ E.logOutputs = (D j).rate ∧
      1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
      (E.a * E.b * E.c) ^ 2 =
        5 ^ (k ^ 2 * ∑ i : Fin 3, ∑ c, (L.packet j).mu i c (fun _ ↦ 1)) := by
    intro j
    obtain ⟨x, hs, ht, hx⟩ := packet_exact_supported (L.packet j) k hkpos (delta j) (hd j).le
    obtain ⟨E, hi, hr, ha, hb, hc, hv⟩ :=
      mme_elementary_supported_stage_exact_volume (D j) (by decide : 1 < 2) x hs ht
    refine ⟨E, hi, hr, ha, hb, hc, ?_⟩
    rw [hv]
    congr 1
    calc
      _ = ∑ i : Fin 3, ∑ c, (L.packet j).histogram k (x i) c (fun _ ↦ 1) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (histogram_one_count (fullCell (L.packet j).total ((L.packet j).address k))
          (MME.DWZProfiledRegional.positionsAt (L.packet j).n (k ^ 2)) rfl (x i)).symm
      _ = ∑ i : Fin 3, ∑ c, k ^ 2 * (L.packet j).mu i c (fun _ ↦ 1) := by
        simp_rw [hx]
      _ = _ := by simp only [Finset.mul_sum]
  choose E hE using hparts
  let R : LogJointRecipeG (N k) 2 ((layerWindow L).source eps k) :=
    .partition (fun j ↦ (L.packet j).size k) (L.positions k)
      (fun j ↦ (L.packet j).source eps k) (by
        intro i x h
        exact (layer_window_source_iff L eps k i x).mpr h) E
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (∏ j, (E j).inputs) = 1
    simp only [fun j ↦ (hE j).1, Finset.prod_const_one]
  · change (∑ j, (E j).logOutputs) = L.rate * k ^ 2
    simp only [fun j ↦ (hE j).2.1, hr]
    exact (Finset.sum_mul _ _ _).symm
  · change 1 ≤ ∏ j, (E j).a
    exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.1)
  · change 1 ≤ ∏ j, (E j).b
    exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.2.1)
  · change 1 ≤ ∏ j, (E j).c
    exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.2.2.1)
  · change ((∏ j, (E j).a) * (∏ j, (E j).b) * (∏ j, (E j).c)) ^ 2 = _
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    simp_rw [fun j ↦ (hE j).2.2.2.2.2]
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
private theorem common_radius {p : ℕ} (delta : Fin p → ℝ) (hd : ∀ j, 0 < delta j) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ j, eps ≤ delta j := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image delta)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨s.inf' hs id, (Finset.lt_inf'_iff hs).mpr ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · simpa only [hx] using (show (0 : ℝ) < 1 by norm_num)
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact hd j
  · intro j
    exact Finset.inf'_le id (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨j, Finset.mem_univ j, rfl⟩))

private theorem routing_target {ell : ℕ} {N : ℕ → ℕ} {L : Layer ell N}
    {W : Window N} (H : Routing L W) (eps : ℝ) (he : 0 ≤ eps)
    (delta : Fin L.parts → ℝ) (hed : ∀ j, eps * H.bound ≤ delta j) (k : ℕ) :
    ∀ i x, W.source eps k i x →
      ∀ j, (L.packet j).target (delta j) k i (L.piece k x j) := by
  classical
  intro i x hx j
  refine ⟨H.grade_identity k i x hx.1 j, ?_, ?_⟩
  · intro c
    rw [packet_histogram_mass, ← Finset.mul_sum, (L.packet j).mu_mass]
    rfl
  · intro c w
    have hb : |∑ o, H.weight i j c w o * (W.observe k i x o - W.center i o)| ≤
        eps * H.bound := by
      calc
        _ ≤ ∑ o, |H.weight i j c w o * (W.observe k i x o - W.center i o)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ o, H.weight i j c w o * |W.observe k i x o - W.center i o| := by
          apply Finset.sum_congr rfl
          intro o _
          rw [abs_mul, abs_of_nonneg (H.nonneg i j c w o)]
        _ ≤ ∑ o, H.weight i j c w o * eps := Finset.sum_le_sum
          (fun o _ ↦ mul_le_mul_of_nonneg_left (hx.2 o).le (H.nonneg i j c w o))
        _ = (∑ o, H.weight i j c w o) * eps := (Finset.sum_mul _ _ _).symm
        _ ≤ H.bound * eps := mul_le_mul_of_nonneg_right (H.row_le i j c w) he
        _ = _ := mul_comm _ _
    have hid : ((L.packet j).histogram k (L.piece k x j) c w : ℝ) -
        ((k ^ 2 * (L.packet j).mu i c w : ℕ) : ℝ) =
        ((k ^ 2 * (L.packet j).mass c : ℕ) : ℝ) *
          ∑ o, H.weight i j c w o * (W.observe k i x o - W.center i o) := by
      rw [H.count_identity k i x j c w, Nat.cast_mul, Nat.cast_mul,
        H.center_identity i j c w]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hm : (∑ z, k ^ 2 * (L.packet j).mu i c z : ℕ) =
        k ^ 2 * (L.packet j).mass c := by
      rw [← Finset.mul_sum, (L.packet j).mu_mass]
      rfl
    rw [hm]
    exact (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)).trans
      (by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right (hed j) (Nat.cast_nonneg (k ^ 2 * (L.packet j).mass c)))

private theorem extend_layer {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N)
    (eps : ℝ) (delta : Fin L.parts → ℝ) (k : ℕ)
    (D : ∀ j, LogPartStageG ((L.packet j).size k) ell
      ((L.packet j).source eps k) ((L.packet j).target (delta j) k))
    (hp : ∀ j, 1 ≤ (D j).types ∧ (D j).types ≤ (k + 1) ^ (L.packet j).degree)
    (hr : ∀ j, (D j).rate = (L.packet j).rate * k ^ 2)
    (Q : Predicate (N k))
    (ht : ∀ i x, Q i x → ∀ j, (L.packet j).target (delta j) k i (L.piece k x j))
    (next : LogJointRecipeG (N k) ell Q) (degree : ℕ)
    (hn : 1 ≤ next.inputs ∧ next.inputs ≤ (k + 1) ^ degree) :
    ∃ E : LogJointRecipeG (N k) (ell + 1) ((layerWindow L).source eps k),
      1 ≤ E.inputs ∧ E.inputs ≤ (k + 1) ^ (L.degree + degree) ∧
      E.logOutputs = L.rate * k ^ 2 + next.logOutputs ∧
      E.a = next.a ∧ E.b = next.b ∧ E.c = next.c := by
  classical
  let E : LogJointRecipeG (N k) (ell + 1) ((layerWindow L).source eps k) :=
    .stage (Nat.lt_succ_self ell) (fun j ↦ (L.packet j).size k) (L.positions k)
      (fun j ↦ (L.packet j).source eps k) (fun j ↦ (L.packet j).target (delta j) k)
      (by
        intro i x h
        exact (layer_window_source_iff L eps k i x).mpr h) D ht next
  refine ⟨E, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · change 1 ≤ (∏ j, (D j).types) * next.inputs
    exact one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' (fun j _ ↦ (hp j).1)) hn.1
  · change (∏ j, (D j).types) * next.inputs ≤ _
    calc
      _ ≤ (∏ j, (k + 1) ^ (L.packet j).degree) * (k + 1) ^ degree :=
        Nat.mul_le_mul (Finset.prod_le_prod' (fun j _ ↦ (hp j).2)) hn.2
      _ = (k + 1) ^ (L.degree + degree) := by
        rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
        rfl
  · change (∑ j, (D j).rate) + next.logOutputs = _
    simp only [hr]
    rw [← Finset.sum_mul]
    rfl

/-- Finite regional profile trees with early boundary leaves compile at every
sufficiently large common square scale, with explicit rates and input degree. -/
theorem solution
    {ell : ℕ} {N : ℕ → ℕ} {W : Window N} (C : Certificate ell N W)
    (eps delta : ℝ) (he : 0 < eps) (hd : 0 < delta) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∃ E : LogJointRecipeG (N k) ell (W.source eps k),
        1 ≤ E.inputs ∧ E.inputs ≤ (k + 1) ^ C.degree ∧
        E.logOutputs = C.rate * k ^ 2 ∧
        1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
        (k ^ 2 : ℝ) * (C.volumeRate - delta) ≤
          Real.log ((E.a * E.b * E.c : ℕ) : ℝ) := by
  classical
  induction C generalizing eps delta with
  | boundary B =>
    obtain ⟨k0, h⟩ := mme_boundary_profile_layer_eventual_recipe B eps delta he hd
    refine ⟨k0, ?_⟩
    intro k hk
    obtain ⟨E, hi, hr, ha, hb, hc, hv⟩ := h k hk
    refine ⟨E, by omega, ?_, ?_, ha, hb, hc, hv⟩
    · simp only [Certificate.degree, pow_zero, hi, le_refl]
    · simpa only [Certificate.rate, zero_mul] using hr
  | elementary L =>
    obtain ⟨k0, h⟩ := terminal_layer L eps he
    refine ⟨k0, ?_⟩
    intro k hk
    obtain ⟨E, hi, hr, ha, hb, hc, hv⟩ := h k hk
    refine ⟨E, by omega, ?_, hr, ha, hb, hc, ?_⟩
    · simp only [Certificate.degree, pow_zero, hi, le_refl]
    · have hlog := congrArg (fun n : ℕ ↦ Real.log (n : ℝ)) hv
      simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul] at hlog
      simp only [Certificate.volumeRate, Nat.cast_mul]
      have hnonneg := mul_nonneg (sq_nonneg (k : ℝ)) hd.le
      nlinarith [hlog]
  | descend L next H ih =>
    obtain ⟨ds, hds, ks, hs⟩ := layer_stages L eps he
    obtain ⟨d, hdpos, hsmall⟩ := common_radius ds hds
    let e := d / (H.bound + 1)
    have hepos : 0 < e := div_pos hdpos (by linarith [H.bound_nonneg])
    have heb : e * H.bound ≤ d := by
      have hid : e * (H.bound + 1) = d := by
        dsimp only [e]
        field_simp [ne_of_gt (show 0 < H.bound + 1 by linarith [H.bound_nonneg])]
      nlinarith [hepos.le]
    obtain ⟨kn, hn⟩ := ih e delta hepos hd
    refine ⟨max ks kn, ?_⟩
    intro k hk
    obtain ⟨D, hp, hr⟩ := hs k ((le_max_left _ _).trans hk)
    obtain ⟨E, hi, hb, hrE, ha, hbE, hc, hv⟩ := hn k ((le_max_right _ _).trans hk)
    obtain ⟨R, hRi, hRb, hRr, hRa, hRbb, hRc⟩ :=
      extend_layer L eps ds k D hp hr _
        (routing_target H e hepos.le ds (fun j ↦ heb.trans (hsmall j)) k)
        E next.degree ⟨hi, hb⟩
    refine ⟨R, hRi, hRb, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Certificate.rate, hRr, hrE]
      ring
    · simpa only [hRa] using ha
    · simpa only [hRbb] using hbE
    · simpa only [hRc] using hc
    · simpa only [Certificate.volumeRate, hRa, hRbb, hRc] using hv
  | @partition ell N parts Ns positions Ws children ih =>
    let d := delta / (parts + 1 : ℕ)
    have hdpos : 0 < d := div_pos hd (by positivity)
    choose k0 hk0 using fun j ↦ ih j eps d he hdpos
    refine ⟨Finset.univ.sup k0, ?_⟩
    intro k hk
    have hparts := fun j ↦ hk0 j k ((Finset.le_sup (f := k0) (Finset.mem_univ j)).trans hk)
    choose E hE using hparts
    let R : LogJointRecipeG (N k) ell ((Window.partition Ns positions Ws).source eps k) :=
      .partition (fun j ↦ Ns j k) (positions k) (fun j ↦ (Ws j).source eps k)
        (by
          intro i x h
          exact ⟨fun j ↦ (h j).1, fun o ↦ (h o.1).2 o.2⟩) E
    refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change 1 ≤ ∏ j, (E j).inputs
      exact Finset.one_le_prod' (fun j _ ↦ (hE j).1)
    · change (∏ j, (E j).inputs) ≤ (k + 1) ^ (∑ j, (children j).degree)
      calc
        _ ≤ ∏ j, (k + 1) ^ (children j).degree :=
          Finset.prod_le_prod' (fun j _ ↦ (hE j).2.1)
        _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
    · change (∑ j, (E j).logOutputs) = (∑ j, (children j).rate) * k ^ 2
      simp only [fun j ↦ (hE j).2.2.1, Finset.sum_mul]
    · change 1 ≤ ∏ j, (E j).a
      exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.2.1)
    · change 1 ≤ ∏ j, (E j).b
      exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.2.2.1)
    · change 1 ≤ ∏ j, (E j).c
      exact Finset.one_le_prod' (fun j _ ↦ (hE j).2.2.2.2.2.1)
    · change (k ^ 2 : ℝ) * ((∑ j, (children j).volumeRate) - delta) ≤
        Real.log (((∏ j, (E j).a) * (∏ j, (E j).b) * (∏ j, (E j).c) : ℕ) : ℝ)
      rw [mixed_partition_log_volume _ _ _
        (fun j ↦ (hE j).2.2.2.1) (fun j ↦ (hE j).2.2.2.2.1)
        (fun j ↦ (hE j).2.2.2.2.2.1)]
      have hsum := Finset.sum_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin parts))) ↦ (hE j).2.2.2.2.2.2)
      have hloss : (parts : ℝ) * d ≤ delta := by
        have heq : d * ((parts : ℝ) + 1) = delta := by
          dsimp only [d]
          push_cast
          field_simp
        nlinarith [hdpos.le]
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      exact (mul_le_mul_of_nonneg_left (by linarith :
        (∑ j, (children j).volumeRate) - delta ≤
        (∑ j, (children j).volumeRate) - (parts : ℝ) * d)
        (sq_nonneg (k : ℝ))).trans hsum

#print axioms solution
