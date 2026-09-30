-- Prove2me | solution 1 for zarankiewicz_problem_k33
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-06T05:08:42.057972+00:00
-- url     : https://prove2.me/submissions/29fb38d9-4e11-4339-85a1-3d6db1e4162a

import Mathlib


variable {K : Type*} [Field K]

/-- vectors in `K³` -/
abbrev ZarV (K : Type*) := K × K × K

/-- the quadratic form `v₁ v₂ + v₃²` -/
def zarQ (v : ZarV K) : K := v.1 * v.2.1 + v.2.2 ^ 2
/-- its polar form (twice the symmetric bilinear form): `zarQ(u+w) = zarQ u + zarB u w + zarQ w` -/
def zarB (u w : ZarV K) : K := u.1 * w.2.1 + u.2.1 * w.1 + 2 * u.2.2 * w.2.2
def zarCross (a b : ZarV K) : ZarV K :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)
def zarDot (a b : ZarV K) : K := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2
/-- `zarDot (zarM u) w = zarB u w` -/
def zarM (v : ZarV K) : ZarV K := (v.2.1, v.1, 2 * v.2.2)

lemma zarQ_add (u w : ZarV K) : zarQ (u + w) = zarQ u + zarB u w + zarQ w := by
  simp only [zarQ, zarB, Prod.fst_add, Prod.snd_add]; ring

lemma zarQ_neg (u : ZarV K) : zarQ (-u) = zarQ u := by
  simp only [zarQ, Prod.fst_neg, Prod.snd_neg]; ring

lemma zarQ_smul (t : K) (u : ZarV K) : zarQ (t • u) = t ^ 2 * zarQ u := by
  simp only [zarQ, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma zarB_smul_right (t : K) (u w : ZarV K) : zarB u (t • w) = t * zarB u w := by
  simp only [zarB, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma zarB_comm (u w : ZarV K) : zarB u w = zarB w u := by
  simp only [zarB]; ring

lemma zarB_add_left (u v w : ZarV K) : zarB (u + v) w = zarB u w + zarB v w := by
  simp only [zarB, Prod.fst_add, Prod.snd_add]; ring

lemma dot_comm' (a b : ZarV K) : zarDot a b = zarDot b a := by
  simp only [zarDot]; ring

lemma zarDot_M (u w : ZarV K) : zarDot (zarM u) w = zarB u w := by
  simp only [zarDot, zarM, zarB]; ring

lemma zarM_smul (t : K) (u : ZarV K) : zarM (t • u) = t • zarM u := by
  simp only [zarM, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk, mul_left_comm]

lemma zarM_inj (h2 : (2 : K) ≠ 0) {u v : ZarV K} (h : zarM u = zarM v) : u = v := by
  obtain ⟨u1, u2, u3⟩ := u
  obtain ⟨v1, v2, v3⟩ := v
  simp only [zarM, Prod.mk.injEq] at h
  obtain ⟨h1, h2', h3⟩ := h
  simp only [Prod.mk.injEq]
  refine ⟨h2', h1, ?_⟩
  exact mul_left_cancel₀ h2 h3

/-- Key lemma: if `u ≠ 0` is isotropic and `w ⊥ u` then `zarQ w` is a square. -/
lemma zar_lemA (u w : ZarV K) (hu : u ≠ 0) (hQ : zarQ u = 0) (hB : zarB u w = 0) : IsSquare (zarQ w) := by
  obtain ⟨u1, u2, u3⟩ := u
  obtain ⟨w1, w2, w3⟩ := w
  simp only [zarQ, zarB] at *
  by_cases h1 : u1 = 0
  · by_cases h2 : u2 = 0
    · exfalso
      subst h1 h2
      simp at hQ
      apply hu
      simp [hQ]
    · refine ⟨(u3 * w2 - u2 * w3) / u2, ?_⟩
      field_simp
      linear_combination (u2 * w2) * hB - w2 ^ 2 * hQ
  · refine ⟨(u3 * w1 - u1 * w3) / u1, ?_⟩
    field_simp
    linear_combination (u1 * w1) * hB - w1 ^ 2 * hQ

/-- zarCross product zero implies parallel -/
lemma zar_par_of_cross_eq_zero (z y : ZarV K) (hz : z ≠ 0) (h : zarCross z y = 0) : ∃ s : K, y = s • z := by
  obtain ⟨z1, z2, z3⟩ := z
  obtain ⟨y1, y2, y3⟩ := y
  simp only [zarCross, Prod.mk_eq_zero] at h
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hz1 : z1 = 0
  · by_cases hz2 : z2 = 0
    · have hz3 : z3 ≠ 0 := by
        intro hz3; apply hz; simp [hz1, hz2, hz3]
      refine ⟨y3 / z3, ?_⟩
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · field_simp; linear_combination h2
      · field_simp; linear_combination -h1
      · field_simp
    · refine ⟨y2 / z2, ?_⟩
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · field_simp; linear_combination -h3
      · field_simp
      · field_simp; linear_combination h1
  · refine ⟨y1 / z1, ?_⟩
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · field_simp
    · field_simp; linear_combination h3
    · field_simp; linear_combination -h2

/-- a vector orthogonal to two non-parallel vectors is parallel to their zarCross product -/
lemma zar_perp_two (n1 n2 y : ZarV K) (hN : zarCross n1 n2 ≠ 0) (h1 : zarDot n1 y = 0) (h2 : zarDot n2 y = 0) :
    ∃ s : K, y = s • zarCross n1 n2 := by
  apply zar_par_of_cross_eq_zero _ _ hN
  obtain ⟨a1, a2, a3⟩ := n1
  obtain ⟨b1, b2, b3⟩ := n2
  obtain ⟨y1, y2, y3⟩ := y
  simp only [zarCross, zarDot] at *
  simp only [Prod.mk_eq_zero]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination b1 * h1 - a1 * h2
  · linear_combination b2 * h1 - a2 * h2
  · linear_combination b3 * h1 - a3 * h2

/-- The configuration lemma: three distinct "centers" `0, β, γ` and three distinct "points"
`w, w+δ, w+ε` (relative coordinates) cannot be pairwise at `zarQ`-distance `d` when `d` is a
non-square. -/
lemma zar_no_k33 (h2 : (2 : K) ≠ 0) (d : K) (hd : ¬ IsSquare d) (w β γ δ ε : ZarV K)
    (hβ : β ≠ 0) (hγ : γ ≠ 0) (hβγ : β ≠ γ) (hδ : δ ≠ 0) (hε : ε ≠ 0) (hδε : δ ≠ ε)
    (e1 : zarQ w = d) (e2 : zarQ (w + β) = d) (e3 : zarQ (w + γ) = d)
    (e4 : zarQ (w + δ) = d) (e5 : zarQ (w + β + δ) = d) (e6 : zarQ (w + γ + δ) = d)
    (e7 : zarQ (w + ε) = d) (e8 : zarQ (w + β + ε) = d) (e9 : zarQ (w + γ + ε) = d) : False := by
  simp only [zarQ_add, zarB_add_left] at e2 e3 e4 e5 e6 e7 e8 e9
  have hwβ : zarB w β + zarQ β = 0 := by linear_combination e2 - e1
  have hwγ : zarB w γ + zarQ γ = 0 := by linear_combination e3 - e1
  have hwδ : zarB w δ + zarQ δ = 0 := by linear_combination e4 - e1
  have hwε : zarB w ε + zarQ ε = 0 := by linear_combination e7 - e1
  have hβδ : zarB β δ = 0 := by linear_combination e5 - e2 - hwδ
  have hγδ : zarB γ δ = 0 := by linear_combination e6 - e3 - hwδ
  have hβε : zarB β ε = 0 := by linear_combination e8 - e2 - hwε
  have hγε : zarB γ ε = 0 := by linear_combination e9 - e3 - hwε
  by_cases hpar : ∃ t : K, γ = t • β
  · obtain ⟨t, rfl⟩ := hpar
    have ht0 : t ≠ 0 := by rintro rfl; simp at hγ
    have ht1 : t ≠ 1 := by rintro rfl; simp at hβγ
    rw [zarB_smul_right, zarQ_smul] at hwγ
    have hQβ : zarQ β = 0 := by
      have : t * (t - 1) * zarQ β = 0 := by linear_combination hwγ - t * hwβ
      rcases mul_eq_zero.mp this with h | h
      · exfalso
        rcases mul_eq_zero.mp h with h | h
        · exact ht0 h
        · exact ht1 (sub_eq_zero.mp h)
      · exact h
    have hBβ : zarB β w = 0 := by rw [zarB_comm]; linear_combination hwβ - hQβ
    exact hd (e1 ▸ zar_lemA β w hβ hQβ hBβ)
  · have hN : zarCross β γ ≠ 0 := fun h => hpar (zar_par_of_cross_eq_zero β γ hβ h)
    obtain ⟨s, hs⟩ := zar_perp_two β γ (zarM δ) hN (by rw [dot_comm', zarDot_M, zarB_comm]; exact hβδ)
      (by rw [dot_comm', zarDot_M, zarB_comm]; exact hγδ)
    obtain ⟨s', hs'⟩ := zar_perp_two β γ (zarM ε) hN (by rw [dot_comm', zarDot_M, zarB_comm]; exact hβε)
      (by rw [dot_comm', zarDot_M, zarB_comm]; exact hγε)
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp only [zero_smul] at hs
      apply hδ
      exact zarM_inj h2 (hs.trans (by simp [zarM]; rfl))
    have hεδ : ε = (s' / s) • δ := by
      apply zarM_inj h2
      rw [zarM_smul, hs', hs, smul_smul, div_mul_cancel₀ _ hs0]
    set t := s' / s with ht
    have ht0 : t ≠ 0 := by rintro h; rw [h, zero_smul] at hεδ; exact hε hεδ
    have ht1 : t ≠ 1 := by rintro h; rw [h, one_smul] at hεδ; exact hδε hεδ.symm
    rw [hεδ, zarB_smul_right, zarQ_smul] at hwε
    have hQδ : zarQ δ = 0 := by
      have : t * (t - 1) * zarQ δ = 0 := by linear_combination hwε - t * hwδ
      rcases mul_eq_zero.mp this with h | h
      · exfalso
        rcases mul_eq_zero.mp h with h | h
        · exact ht0 h
        · exact ht1 (sub_eq_zero.mp h)
      · exact h
    have hBδ : zarB δ w = 0 := by rw [zarB_comm]; linear_combination hwδ - hQδ
    exact hd (e1 ▸ zar_lemA δ w hδ hQδ hBδ)


section Graph

variable (p : ℕ) [hp : Fact p.Prime]

/-- the vertex set `(ZMod p)³` -/
abbrev ZarW (p : ℕ) := ZMod p × ZMod p × ZMod p

lemma zarCard_W : Fintype.card (ZarW p) = p ^ 3 := by
  simp [Fintype.card_prod, ZMod.card]; ring

/-- a bijection from `Fin (card ZarW)` to `ZarW` -/
noncomputable def zarEqv : Fin (Fintype.card (ZarW p)) ≃ ZarW p := (Fintype.equivFin (ZarW p)).symm

/-- Brown-type zarGraph: `i ~ j` iff `zarQ (e i - e j) = d` (`d` a non-square). -/
noncomputable def zarGraph (d : ZMod p) (hd : ¬ IsSquare d) :
    SimpleGraph (Fin (Fintype.card (ZarW p))) where
  Adj i j := zarQ (zarEqv p i - zarEqv p j) = d
  symm := fun i j h => by
    show zarQ (zarEqv p j - zarEqv p i) = d
    rw [← neg_sub, zarQ_neg]; exact h
  loopless := ⟨fun i h => by
    simp only [sub_self] at h
    apply hd
    rw [← h]
    exact ⟨0, by simp [zarQ]⟩⟩

noncomputable instance (d : ZMod p) (hd : ¬ IsSquare d) : DecidableRel (zarGraph p d hd).Adj :=
  fun i j => inferInstanceAs (Decidable (zarQ (zarEqv p i - zarEqv p j) = d))

lemma zar_k33free (hp2 : p ≠ 2) (d : ZMod p) (hd : ¬ IsSquare d) :
    ¬∃ (A zarB : Finset (Fin (Fintype.card (ZarW p)))), A.card = 3 ∧ zarB.card = 3 ∧
      ∀ a ∈ A, ∀ b ∈ zarB, (zarGraph p d hd).Adj a b := by
  rintro ⟨A, zarB, hA, hB, hadj⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hA
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hB
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at hadj
  obtain ⟨⟨hax, hay, haz⟩, ⟨hbx, hby, hbz⟩, ⟨hcx, hcy, hcz⟩⟩ := hadj
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have einj : Function.Injective (zarEqv p) := (zarEqv p).injective
  have hax' : zarQ (zarEqv p a - zarEqv p x) = d := hax
  have hay' : zarQ (zarEqv p a - zarEqv p y) = d := hay
  have haz' : zarQ (zarEqv p a - zarEqv p z) = d := haz
  have hbx' : zarQ (zarEqv p b - zarEqv p x) = d := hbx
  have hby' : zarQ (zarEqv p b - zarEqv p y) = d := hby
  have hbz' : zarQ (zarEqv p b - zarEqv p z) = d := hbz
  have hcx' : zarQ (zarEqv p c - zarEqv p x) = d := hcx
  have hcy' : zarQ (zarEqv p c - zarEqv p y) = d := hcy
  have hcz' : zarQ (zarEqv p c - zarEqv p z) = d := hcz
  refine zar_no_k33 h2 d hd (zarEqv p a - zarEqv p x) (zarEqv p b - zarEqv p a) (zarEqv p c - zarEqv p a)
    (zarEqv p x - zarEqv p y) (zarEqv p x - zarEqv p z) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact sub_ne_zero.mpr (einj.ne hab.symm)
  · exact sub_ne_zero.mpr (einj.ne hac.symm)
  · intro h; exact hbc (einj (sub_left_inj.mp h))
  · exact sub_ne_zero.mpr (einj.ne hxy)
  · exact sub_ne_zero.mpr (einj.ne hxz)
  · intro h; exact hyz (einj (sub_right_inj.mp h))
  · exact hax'
  · convert hbx' using 2; abel
  · convert hcx' using 2; abel
  · convert hay' using 2; abel
  · convert hby' using 2; abel
  · convert hcy' using 2; abel
  · convert haz' using 2; abel
  · convert hbz' using 2; abel
  · convert hcz' using 2; abel

lemma zar_degree_ge (d : ZMod p) (hd : ¬ IsSquare d) (i : Fin (Fintype.card (ZarW p))) :
    (p - 1) * p ≤ (zarGraph p d hd).degree i := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have key : ((Finset.univ.erase (0 : ZMod p)) ×ˢ (Finset.univ : Finset (ZMod p))).card
      = (p - 1) * p := by
    rw [Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card]
  rw [← key]
  refine Finset.card_le_card_of_injOn
    (fun z => (zarEqv p).symm (zarEqv p i - (z.1, (d - z.2 ^ 2) / z.1, z.2))) ?_ ?_
  · intro z hz
    have hz1 : z.1 ≠ 0 := by
      have := (Finset.mem_product.mp (Finset.mem_coe.mp hz)).1
      exact Finset.ne_of_mem_erase this
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
    show zarQ (zarEqv p i - zarEqv p ((zarEqv p).symm _)) = d
    rw [Equiv.apply_symm_apply, sub_sub_cancel]
    simp only [zarQ]
    field_simp
    ring
  · intro z hz z' hz' heq
    simp only at heq
    have h1 := (zarEqv p).symm.injective heq
    have h2 := sub_right_injective h1
    rw [Prod.mk.injEq, Prod.mk.injEq] at h2
    exact Prod.ext h2.1 h2.2.2

lemma zar_edge_bound (d : ZMod p) (hd : ¬ IsSquare d) :
    p ^ 3 * ((p - 1) * p) ≤ 2 * (zarGraph p d hd).edgeFinset.card := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc p ^ 3 * ((p - 1) * p) = ∑ i : Fin (Fintype.card (ZarW p)), ((p - 1) * p) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, zarCard_W, smul_eq_mul]
    _ ≤ ∑ i, (zarGraph p d hd).degree i := Finset.sum_le_sum (fun i _ => zar_degree_ge p d hd i)

end Graph


theorem solution : ¬ (∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (¬∃ (A B : Finset (Fin n)), A.card = 3 ∧ B.card = 3 ∧
        ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) →
      G.edgeFinset.card ≤ C * n ^ (3/2 + eps)) := by
  intro h
  obtain ⟨C, hC, hG⟩ := h (1/12) (by norm_num)
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (⌈(4 * C) ^ 4⌉₊ + 16)
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨d, hd⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact_mod_cast hp2)
  have hE := hG _ (zarGraph p d hd) (zar_k33free p hp2 d hd)
  have hE2 := zar_edge_bound p d hd
  have hcast : ((Fintype.card (ZarW p) : ℕ) : ℝ) = ((p ^ 3 : ℕ) : ℝ) := by rw [zarCard_W]
  rw [hcast] at hE
  set E : ℕ := (zarGraph p d hd).edgeFinset.card with hEdef
  -- real arithmetic
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set q : ℝ := (p : ℝ) ^ ((1 : ℝ) / 4) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hp0 _
  have hq4 : q ^ 4 = p := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hp0]
    have h14 : ((1 : ℝ) / 4) * ((4 : ℕ) : ℝ) = 1 := by norm_num
    rw [h14, Real.rpow_one]
  have hn : ((p ^ 3 : ℕ) : ℝ) ^ ((3 : ℝ) / 2 + 1 / 12) = q ^ 19 := by
    rw [Nat.cast_pow, ← hq4, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hq0]
    have h19 : ((4 * 3 : ℕ) : ℝ) * ((3 : ℝ) / 2 + 1 / 12) = ((19 : ℕ) : ℝ) := by norm_num
    rw [h19, Real.rpow_natCast]
  have hE' : (E : ℝ) ≤ C * q ^ 19 := by
    rw [← hn]; exact_mod_cast hE
  have hE2' : (p : ℝ) ^ 3 * (((p : ℝ) - 1) * p) ≤ 2 * (E : ℝ) := by
    have h1 : ((p ^ 3 * ((p - 1) * p) : ℕ) : ℝ) ≤ ((2 * E : ℕ) : ℝ) := by exact_mod_cast hE2
    push_cast [Nat.cast_sub hp.one_lt.le] at h1
    exact h1
  rw [← hq4] at hE2'
  have hpC : (4 * C) ^ 4 < (p : ℝ) := by
    have h1 : (4 * C) ^ 4 ≤ (⌈(4 * C) ^ 4⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(4 * C) ^ 4⌉₊ + 16 : ℕ) : ℝ) ≤ p := by exact_mod_cast hpge
    push_cast at h2
    linarith
  have hp16 : (16 : ℝ) ≤ p := by
    have h2 : ((⌈(4 * C) ^ 4⌉₊ + 16 : ℕ) : ℝ) ≤ p := by exact_mod_cast hpge
    push_cast at h2
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌈(4 * C) ^ 4⌉₊)]
  rw [← hq4] at hpC hp16
  have hCq : 4 * C < q := lt_of_pow_lt_pow_left₀ 4 hq0 hpC
  have hq2 : (2 : ℝ) ≤ q := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hq0 ?_
    norm_num
    linarith
  have hqpos : 0 < q := by linarith
  have k1 : 4 * C * q ^ 19 < q * q ^ 19 := mul_lt_mul_of_pos_right hCq (pow_pos hqpos 19)
  have k2 : (16 : ℝ) ≤ q ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hq2 4
    norm_num at this; linarith
  have k3 : 16 * q ^ 16 ≤ q ^ 4 * q ^ 16 := mul_le_mul_of_nonneg_right k2 (pow_nonneg hq0 16)
  have k4 : (0 : ℝ) ≤ q ^ 16 := pow_nonneg hq0 16
  nlinarith [k1, k3, k4, hE', hE2']
