-- Prove2me | solution 1 for DataSheafCohomology.cyc_ker_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T17:19:25.919673+00:00
-- url     : https://prove2.me/submissions/f46a1a34-fed8-4627-ac81-8eb70c5454db

import Mathlib
import Definitions.Def_Algebra_DataSheafCohomology

open DataSheafCohomology Finset

variable {K : Type*} [Field K] {m : ℕ}

private lemma mem_ker_cycD {a : ℕ → K} {f : Fin (m + 1) → K} :
    f ∈ LinearMap.ker (cycD m a) ↔
      ∀ i : Fin (m + 1), a i.val * f (i + 1) = f i := by
  simp only [LinearMap.mem_ker, cycD, LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · intro h i
    have h2 := congrFun h i
    simp only [Pi.zero_apply] at h2
    exact eq_of_sub_eq_zero h2
  · intro h
    funext i
    simp [h i]

private lemma cyc_succ_mk {k : ℕ} (h : k + 1 < m + 1) :
    (⟨k, by omega⟩ + 1 : Fin (m + 1)) = ⟨k + 1, h⟩ := by
  have hlt : (⟨k, by omega⟩ : Fin (m + 1)) < Fin.last m := by
    simp [Fin.lt_def]
    omega
  ext
  rw [Fin.val_add_one_of_lt hlt]

private lemma cyc_last_succ {k : ℕ} (hk : k < m + 1) (h : k = m) :
    (⟨k, hk⟩ + 1 : Fin (m + 1)) = 0 := by
  have hlast : (⟨k, hk⟩ : Fin (m + 1)) = Fin.last m := by
    ext
    simpa using h
  rw [hlast, Fin.last_add_one]

private lemma cyc_prod_ne_zero {a : ℕ → K} (ha : ∀ j, j < m + 1 → a j ≠ 0)
    {k : ℕ} (hk : k ≤ m + 1) : (∏ j ∈ range k, a j) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j hj =>
    ha j (lt_of_lt_of_le (Finset.mem_range.1 hj) hk)

/-- Parallel transport along the cycle (inlined; not present in the skeleton Def). -/
private lemma ker_transport {a : ℕ → K} {f : Fin (m + 1) → K}
    (hf : ∀ i : Fin (m + 1), a i.val * f (i + 1) = f i) :
    ∀ k, (hk : k < m + 1) → f ⟨k, hk⟩ * (∏ j ∈ range k, a j) = f 0 := by
  intro k
  induction k with
  | zero => intro hk; simp
  | succ p ih =>
    intro hk
    have hp : p < m + 1 := by omega
    have h1 := hf ⟨p, hp⟩
    rw [cyc_succ_mk hk] at h1
    have h2 := ih hp
    rw [Finset.prod_range_succ]
    calc
      f ⟨p + 1, hk⟩ * ((∏ j ∈ range p, a j) * a p)
          = (a p * f ⟨p + 1, hk⟩) * (∏ j ∈ range p, a j) := by ring
      _ = f ⟨p, hp⟩ * (∏ j ∈ range p, a j) := by rw [h1]
      _ = f 0 := h2

private lemma holonomy_constraint {a : ℕ → K} {f : Fin (m + 1) → K}
    (hf : ∀ i : Fin (m + 1), a i.val * f (i + 1) = f i) :
    holonomy a m * f 0 = f 0 := by
  have hm : m < m + 1 := Nat.lt_succ_self m
  have h1 := hf ⟨m, hm⟩
  rw [cyc_last_succ hm rfl] at h1
  have h2 := ker_transport hf m hm
  unfold holonomy
  rw [Finset.prod_range_succ]
  calc
    (∏ j ∈ range m, a j) * a m * f 0
        = (a m * f 0) * (∏ j ∈ range m, a j) := by ring
    _ = f ⟨m, hm⟩ * (∏ j ∈ range m, a j) := by rw [h1]
    _ = f 0 := h2

theorem solution {a : ℕ → K} (ha : ∀ j, j < m + 1 → a j ≠ 0)
    (hh : holonomy a m ≠ 1) : LinearMap.ker (cycD m a) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hfmem
  have hf := (mem_ker_cycD (a := a) (f := f)).1 hfmem
  have h0 : f 0 = 0 := by
    have hc := holonomy_constraint hf
    have hsub : (holonomy a m - 1) * f 0 = 0 := by
      calc
        (holonomy a m - 1) * f 0
            = holonomy a m * f 0 - f 0 := by ring
        _ = f 0 - f 0 := by rw [hc]
        _ = 0 := by ring
    rcases mul_eq_zero.1 hsub with h | h
    · exact absurd (eq_of_sub_eq_zero h) hh
    · exact h
  funext i
  obtain ⟨k, hk⟩ := i
  have ht := ker_transport hf k hk
  rw [h0, mul_eq_zero] at ht
  have hne := cyc_prod_ne_zero ha (le_of_lt hk)
  exact ht.resolve_right hne
