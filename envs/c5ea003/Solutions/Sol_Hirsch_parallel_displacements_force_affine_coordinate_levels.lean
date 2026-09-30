-- Prove2me | solution 1 for Hirsch.parallel_displacements_force_affine_coordinate_levels
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-16T19:41:22.875815+00:00
-- url     : https://prove2.me/submissions/0801e679-3429-4cee-9e83-57652530224b

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-- Distinct positive signed displacements occupy two different off-diagonal
ordered level pairs each, regardless of the common nonzero scale's sign. -/
private theorem distinct_displacements_count
    {I : Type*} [Fintype I] (L : Finset ℝ)
    (a b lambda : I → ℝ) (c : ℝ)
    (ha : ∀ i, a i ∈ L) (hb : ∀ i, b i ∈ L)
    (hpos : ∀ i, 0 < lambda i) (hinj : Function.Injective lambda)
    (hc : c ≠ 0) (hdiff : ∀ i, b i - a i = lambda i * c) :
    2 * Fintype.card I ≤ L.card * (L.card - 1) := by
  classical
  let forward : I → ℝ × ℝ := fun i => (a i, b i)
  let backward : I → ℝ × ℝ := fun i => (b i, a i)
  have hneq : ∀ i, a i ≠ b i := by
    intro i he
    have h := hdiff i
    rw [he, sub_self] at h
    exact (mul_ne_zero (ne_of_gt (hpos i)) hc) h.symm
  have hf : Function.Injective forward := by
    intro i j he
    apply hinj
    have h : b i - a i = b j - a j :=
      congrArg (fun z : ℝ × ℝ => z.2 - z.1) he
    rw [hdiff i, hdiff j] at h
    have hz : (lambda i - lambda j) * c = 0 := by
      rw [sub_mul, h, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hc)
  have hr : Function.Injective backward := by
    intro i j he
    apply hf
    exact congrArg Prod.swap he
  let F := Finset.univ.image forward
  let B := Finset.univ.image backward
  have hdis : Disjoint F B := by
    apply Finset.disjoint_left.mpr
    intro z hzF hzB
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzF
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hzB
    have he : (a i, b i) = (b j, a j) := hi.trans hj.symm
    have h1 : a i = b j := congrArg Prod.fst he
    have h2 : b i = a j := congrArg Prod.snd he
    have hi' := hdiff i
    have hj' := hdiff j
    have hz : (lambda i + lambda j) * c = 0 := by
      rw [add_mul]
      linarith
    exact (mul_ne_zero (ne_of_gt (add_pos (hpos i) (hpos j))) hc) hz
  have hsub : F ∪ B ⊆ L.offDiag := by
    intro z hz
    rcases Finset.mem_union.mp hz with hF | hB
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hF
      exact Finset.mem_offDiag.mpr ⟨ha i, hb i, hneq i⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
      exact Finset.mem_offDiag.mpr ⟨hb i, ha i, Ne.symm (hneq i)⟩
  have hFcard : F.card = Fintype.card I := by
    exact (Finset.card_image_of_injective Finset.univ hf).trans (Finset.card_univ)
  have hBcard : B.card = Fintype.card I := by
    exact (Finset.card_image_of_injective Finset.univ hr).trans (Finset.card_univ)
  have hcount : 2 * Fintype.card I ≤ L.offDiag.card := by
    calc
      2 * Fintype.card I = F.card + B.card := by rw [hFcard, hBcard]; omega
      _ = (F ∪ B).card := (Finset.card_union_of_disjoint hdis).symm
      _ ≤ L.offDiag.card := Finset.card_le_card hsub
  simpa only [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one] using hcount

/-- A finite family of distinct positive parallel displacements forces many
coordinate levels in every injective affine embedding. Injectivity supplies
the detecting coordinate; its existence is not an extra hypothesis. -/
theorem solution
    {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
    (V : Finset E) (p q : I → E) (g : E) (lambda : I → ℝ)
    (hp : ∀ i, p i ∈ V) (hq : ∀ i, q i ∈ V)
    (hg : g ≠ 0) (hpos : ∀ i, 0 < lambda i)
    (hinj : Function.Injective lambda)
    (hdisp : ∀ i, q i - p i = lambda i • g)
    (r : ℕ) (T : E →ₗ[ℝ] (Fin r → ℝ))
    (hT : Function.Injective T) (offset : Fin r → ℝ) :
    ∃ j : Fin r, (T g) j ≠ 0 ∧
      2 * Fintype.card I ≤
        (V.image (fun x => (T x) j + offset j)).card *
          ((V.image (fun x => (T x) j + offset j)).card - 1) := by
  classical
  have hex : ∃ j : Fin r, (T g) j ≠ 0 := by
    by_contra hn
    have hzero : T g = 0 := by
      funext j
      by_contra hj
      exact hn ⟨j, hj⟩
    exact hg (hT (hzero.trans T.map_zero.symm))
  obtain ⟨j, hj⟩ := hex
  let f : E → ℝ := fun x => (T x) j + offset j
  let L : Finset ℝ := V.image f
  have ha : ∀ i, f (p i) ∈ L := fun i => Finset.mem_image.mpr ⟨p i, hp i, rfl⟩
  have hb : ∀ i, f (q i) ∈ L := fun i => Finset.mem_image.mpr ⟨q i, hq i, rfl⟩
  have hdiff : ∀ i, f (q i) - f (p i) = lambda i * (T g) j := by
    intro i
    calc
      f (q i) - f (p i) = (T (q i - p i)) j := by
        simp only [f, map_sub, Pi.sub_apply]
        ring
      _ = (T (lambda i • g)) j := by rw [hdisp i]
      _ = lambda i * (T g) j := by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  exact ⟨j, hj, distinct_displacements_count L (fun i => f (p i))
    (fun i => f (q i)) lambda ((T g) j) ha hb hpos hinj hj hdiff⟩

#print axioms distinct_displacements_count
#print axioms solution
