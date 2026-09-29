-- Prove2me | solution 1 for KServer.martingale_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T09:35:10.480798+00:00
-- url     : https://prove2.me/submissions/a5c1a2e0-678f-47e2-a53e-d6bb63b305ae

import Mathlib
import Definitions.Def_KServer_discrete_martingale

open Finset KServer

/-! Elementary anti-concentration for finite discrete martingales, replacing
Ibragimov's martingale Berry–Esseen in the BCR lower bound. -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Conditioning: if `f` and `h` are constant on the fibers of `key` and on every
fiber the `P`-weighted sum of `g` equals `h` times the fiber mass, then `f·g` and
`f·h` have the same expectation. -/
private theorem cond_eq (P : Ω → ℝ) (key : Ω → ℕ) (f g h : Ω → ℝ)
    (hf : ∀ ω ω', key ω = key ω' → f ω = f ω')
    (hcl : ∀ ω₀ : Ω, ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω * g ω
      = h ω₀ * ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω)
    (hh : ∀ ω ω', key ω = key ω' → h ω = h ω') :
    ∑ ω, P ω * (f ω * g ω) = ∑ ω, P ω * (f ω * h ω) := by
  classical
  have hfib : ∀ F : Ω → ℝ, ∑ ω, F ω
      = ∑ b ∈ univ.image key, ∑ ω ∈ univ.filter (fun ω => key ω = b), F ω := by
    intro F
    exact (Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image_of_mem key
      (Finset.mem_univ x)) F).symm
  rw [hfib fun ω => P ω * (f ω * g ω), hfib fun ω => P ω * (f ω * h ω)]
  refine Finset.sum_congr rfl ?_
  intro b hb
  obtain ⟨ω₀, -, hω₀⟩ := Finset.mem_image.mp hb
  have hset : (univ.filter fun ω => key ω = b) = univ.filter fun ω => key ω = key ω₀ := by
    rw [hω₀]
  rw [hset]
  have hleft : ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω * (f ω * g ω)
      = f ω₀ * ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω * g ω := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro ω hω
    have hk : key ω = key ω₀ := (Finset.mem_filter.mp hω).2
    rw [hf ω ω₀ hk]
    ring
  have hright : ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω * (f ω * h ω)
      = f ω₀ * (h ω₀ * ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro ω hω
    have hk : key ω = key ω₀ := (Finset.mem_filter.mp hω).2
    rw [hf ω ω₀ hk, hh ω ω₀ hk]
    ring
  rw [hleft, hright, hcl ω₀]

section Martingale

variable (P : Ω → ℝ) (N : ℕ) (hist : ℕ → Ω → ℕ) (X v : ℕ → Ω → ℝ)

variable {P N hist X v}

private theorem S_succ (j : ℕ) (ω : Ω) : mgSum X (j + 1) ω = mgSum X j ω + X j ω := by
  unfold mgSum
  rw [Finset.sum_range_succ]

variable (H : IsDiscreteMartingale P N hist X v)

/-- Partial sums are `hist j`-measurable. -/
private theorem S_meas (H : IsDiscreteMartingale P N hist X v) (j : ℕ) (hj : j ≤ N)
    (ω ω' : Ω) (h : hist j ω = hist j ω') : mgSum X j ω = mgSum X j ω' := by
  unfold mgSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hiN : i < N := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
  exact H.hadapt i hiN ω ω' (H.href (i + 1) j (Finset.mem_range.mp hi) ω ω' h)

/-- Conditional-mean-zero against any `hist j`-measurable weight. -/
private theorem mart_mul (H : IsDiscreteMartingale P N hist X v) (j : ℕ) (hj : j < N)
    (f : Ω → ℝ) (hf : ∀ ω ω', hist j ω = hist j ω' → f ω = f ω') :
    ∑ ω, P ω * (f ω * X j ω) = 0 := by
  have h := cond_eq P (hist j) f (X j) (fun _ => 0) hf
    (fun ω₀ => by rw [zero_mul]; exact H.hmart j hj ω₀) (fun _ _ _ => rfl)
  rw [h]
  simp

/-- Conditional second moment against any `hist j`-measurable weight. -/
private theorem var_mul (H : IsDiscreteMartingale P N hist X v) (j : ℕ) (hj : j < N)
    (f : Ω → ℝ) (hf : ∀ ω ω', hist j ω = hist j ω' → f ω = f ω') :
    ∑ ω, P ω * (f ω * (X j ω) ^ 2) = ∑ ω, P ω * (f ω * v j ω) :=
  cond_eq P (hist j) f (fun ω => (X j ω) ^ 2) (v j) hf
    (fun ω₀ => H.hvar j hj ω₀) (fun ω ω' h => H.hvmeas j hj ω ω' h)

/-- Orthogonality of increments: the second moment is the expected total variance. -/
theorem solution {P : Ω → ℝ} {N : ℕ} {hist : ℕ → Ω → ℕ} {X v : ℕ → Ω → ℝ}
    (H : IsDiscreteMartingale P N hist X v) :
    ∑ ω, P ω * (mgSum X N ω) ^ 2 = ∑ ω, P ω * (∑ j ∈ range N, v j ω) := by
  have key : ∀ k, k ≤ N → ∑ ω, P ω * (mgSum X k ω) ^ 2
      = ∑ ω, P ω * (∑ j ∈ range k, v j ω) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [mgSum]
    | succ k ih =>
      intro hk
      have hkN : k < N := hk
      have hexp : ∀ ω, (mgSum X (k + 1) ω) ^ 2
          = (mgSum X k ω) ^ 2 + 2 * (mgSum X k ω * X k ω) + (X k ω) ^ 2 := by
        intro ω
        rw [S_succ]
        ring
      have h1 : ∑ ω, P ω * (mgSum X (k + 1) ω) ^ 2
          = (∑ ω, P ω * (mgSum X k ω) ^ 2) + 2 * (∑ ω, P ω * (mgSum X k ω * X k ω))
            + ∑ ω, P ω * (X k ω) ^ 2 := by
        have e : ∀ ω : Ω, P ω * (mgSum X (k + 1) ω) ^ 2
            = P ω * (mgSum X k ω) ^ 2 + 2 * (P ω * (mgSum X k ω * X k ω)) + P ω * (X k ω) ^ 2 := by
          intro ω
          rw [S_succ]
          ring
        rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum]
      have h2 : ∑ ω, P ω * (mgSum X k ω * X k ω) = 0 :=
        mart_mul H k hkN (mgSum X k) (S_meas H k (le_of_lt hkN))
      have h3 : ∑ ω, P ω * (X k ω) ^ 2 = ∑ ω, P ω * v k ω := by
        have := var_mul H k hkN (fun _ => 1) (fun _ _ _ => rfl)
        simpa using this
      have h4 : ∑ ω, P ω * (∑ j ∈ range (k + 1), v j ω)
          = (∑ ω, P ω * (∑ j ∈ range k, v j ω)) + ∑ ω, P ω * v k ω := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.sum_range_succ]
        ring
      rw [h1, h2, h3, ih (le_of_lt hkN), h4]
      ring
  exact key N (le_refl N)

end Martingale
